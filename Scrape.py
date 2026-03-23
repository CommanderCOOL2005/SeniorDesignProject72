import argparse
import json
import time
from pathlib import Path
from typing import Iterable

import requests
from bs4 import BeautifulSoup
from tqdm import tqdm
from urllib.parse import urljoin

BASE = "https://proofwiki.org"
DEFAULT_CATEGORY_URL = BASE + "/wiki/Category:Proofs"
API_ENDPOINT = BASE + "/w/api.php"


def fetch_soup(session: requests.Session, url: str) -> BeautifulSoup:
    response = session.get(url, timeout=30)
    response.raise_for_status()
    return BeautifulSoup(response.text, "html.parser")


def category_url_to_title(category_url: str) -> str:
    marker = "/wiki/"
    if marker not in category_url:
        return "Category:Proofs"

    tail = category_url.split(marker, 1)[1]
    if not tail:
        return "Category:Proofs"

    title = tail.replace("_", " ")
    return title


def fetch_category_members(session: requests.Session, category_title: str) -> list[dict]:
    members: list[dict] = []
    cont: dict = {}

    while True:
        params = {
            "action": "query",
            "list": "categorymembers",
            "cmtitle": category_title,
            "cmtype": "page|subcat",
            "cmlimit": "max",
            "format": "json",
        }
        params.update(cont)

        response = session.get(API_ENDPOINT, params=params, timeout=30)
        response.raise_for_status()
        payload = response.json()

        members.extend(payload.get("query", {}).get("categorymembers", []))

        if "continue" not in payload:
            break

        cont = payload["continue"]

    return members


def get_category_links(session: requests.Session, category_url: str, max_links: int | None = None) -> list[str]:
    root_category = category_url_to_title(category_url)
    if not root_category.startswith("Category:"):
        root_category = f"Category:{root_category}"

    page_links: set[str] = set()
    pending_categories: list[str] = [root_category]
    seen_categories: set[str] = set()

    scanned_categories = 0
    while pending_categories:
        current_category = pending_categories.pop(0)
        if current_category in seen_categories:
            continue

        seen_categories.add(current_category)
        scanned_categories += 1
        if scanned_categories % 25 == 0:
            print(
                f"[category-scan] scanned={scanned_categories} pending={len(pending_categories)} pages={len(page_links)}",
                flush=True,
            )
        try:
            members = fetch_category_members(session, current_category)
        except requests.RequestException:
            continue

        for member in members:
            namespace = member.get("ns")
            title = member.get("title", "")
            if not title:
                continue

            if namespace == 14 and title.startswith("Category:"):
                if title not in seen_categories:
                    pending_categories.append(title)
            elif namespace == 0:
                page_links.add(urljoin(BASE, "/wiki/" + title.replace(" ", "_")))
                if max_links is not None and len(page_links) >= max_links:
                    return sorted(page_links)

    return sorted(page_links)


def write_json(path: Path, data: list[dict]) -> None:
    path.write_text(json.dumps(data, ensure_ascii=False, indent=2), encoding="utf-8")


def extract_statement(content: BeautifulSoup) -> str:
    if content is None:
        return ""

    for paragraph in content.find_all("p", recursive=False):
        text = paragraph.get_text(" ", strip=True)
        if text:
            return text

    paragraph = content.find("p")
    return paragraph.get_text(" ", strip=True) if paragraph else ""


def extract_proof(content: BeautifulSoup) -> tuple[str, list[str]]:
    if content is None:
        return "", []

    children = [child for child in content.children if getattr(child, "name", None)]
    proof_start_index = None
    for index, child in enumerate(children):
        if child.name not in {"h2", "h3", "h4"}:
            continue
        heading = child.get_text(" ", strip=True).lower()
        if heading.startswith("proof"):
            proof_start_index = index + 1
            break

    if proof_start_index is None:
        return "", []

    proof_text_parts: list[str] = []
    proof_steps: list[str] = []

    for child in children[proof_start_index:]:
        if child.name in {"h2", "h3", "h4"}:
            break
        if child.name in {"ol", "ul"}:
            for list_item in child.find_all("li", recursive=False):
                text = list_item.get_text(" ", strip=True)
                if text:
                    proof_steps.append(text)
            continue
        if child.name == "p":
            text = child.get_text(" ", strip=True)
            if text:
                proof_text_parts.append(text)

    proof_text = "\n".join(proof_text_parts).strip()
    return proof_text, proof_steps


def scrape_proof(session: requests.Session, url: str) -> dict | None:
    soup = fetch_soup(session, url)
    title_tag = soup.find("h1")
    title = title_tag.get_text(strip=True) if title_tag else ""
    content = soup.select_one("#mw-content-text .mw-parser-output")

    statement = extract_statement(content)
    proof_text, proof_steps = extract_proof(content)

    if not proof_text and not proof_steps:
        return None

    return {
        "url": url,
        "title": title,
        "statement": statement,
        "proof_text": proof_text,
        "proof_steps": proof_steps,
    }


def scrape_all(
    links: Iterable[str],
    delay: float,
    limit: int | None,
    output_path: Path,
    checkpoint_every: int,
) -> list[dict]:
    data: list[dict] = []
    session = requests.Session()
    session.headers.update(
        {
            "User-Agent": "DistillationProofCollector/1.0 (+https://proofwiki.org)",
        }
    )

    checkpoint_path = output_path.with_suffix(output_path.suffix + ".partial")

    for index, link in enumerate(tqdm(links)):
        if limit is not None and index >= limit:
            break
        try:
            item = scrape_proof(session, link)
            if item:
                data.append(item)
                if checkpoint_every > 0 and len(data) % checkpoint_every == 0:
                    write_json(checkpoint_path, data)
                    print(
                        f"[scrape-progress] kept={len(data)} last_url={link}",
                        flush=True,
                    )
            time.sleep(delay)
        except requests.RequestException:
            time.sleep(delay)

    if checkpoint_path.exists():
        checkpoint_path.unlink(missing_ok=True)

    return data


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", default="proofwiki_raw.json")
    parser.add_argument("--delay", type=float, default=0.5)
    parser.add_argument("--limit", type=int, default=None)
    parser.add_argument("--category-url", default=DEFAULT_CATEGORY_URL)
    parser.add_argument("--checkpoint-every", type=int, default=200)
    args = parser.parse_args()

    session = requests.Session()
    session.headers.update(
        {
            "User-Agent": "DistillationProofCollector/1.0 (+https://proofwiki.org)",
        }
    )

    output_path = Path(args.output)
    links = get_category_links(session, args.category_url, max_links=args.limit)
    print(f"[category-scan] total_links={len(links)}", flush=True)

    data = scrape_all(
        links,
        delay=args.delay,
        limit=args.limit,
        output_path=output_path,
        checkpoint_every=args.checkpoint_every,
    )

    write_json(output_path, data)
    print(f"[scrape-complete] kept={len(data)} output={output_path}", flush=True)


if __name__ == "__main__":
    main()