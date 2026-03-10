import argparse
import json
import time
from typing import Iterable

import requests
from bs4 import BeautifulSoup
from tqdm import tqdm
from urllib.parse import urljoin

BASE = "https://proofwiki.org"
DEFAULT_CATEGORY_URL = BASE + "/wiki/Category:Proofs"


def fetch_soup(session: requests.Session, url: str) -> BeautifulSoup:
    response = session.get(url, timeout=30)
    response.raise_for_status()
    return BeautifulSoup(response.text, "html.parser")


def get_category_links(session: requests.Session, category_url: str) -> list[str]:
    links: set[str] = set()
    next_url = category_url
    seen_pages: set[str] = set()

    while next_url and next_url not in seen_pages:
        seen_pages.add(next_url)
        soup = fetch_soup(session, next_url)

        for anchor in soup.select("#mw-pages a[href]"):
            href = anchor.get("href", "")
            if href.startswith("/wiki/") and ":" not in href:
                links.add(urljoin(BASE, href))

        next_link = None
        for anchor in soup.select("#mw-pages a[href]"):
            if anchor.get_text(strip=True).lower() == "next page":
                next_link = urljoin(BASE, anchor["href"])
                break

        next_url = next_link

    return sorted(links)


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

    return {
        "url": url,
        "title": title,
        "statement": statement,
        "proof_text": proof_text,
        "proof_steps": proof_steps,
    }


def scrape_all(links: Iterable[str], delay: float, limit: int | None) -> list[dict]:
    data: list[dict] = []
    session = requests.Session()
    session.headers.update(
        {
            "User-Agent": "DistillationProofCollector/1.0 (+https://proofwiki.org)",
        }
    )

    for index, link in enumerate(tqdm(links)):
        if limit is not None and index >= limit:
            break
        try:
            item = scrape_proof(session, link)
            if item:
                data.append(item)
            time.sleep(delay)
        except requests.RequestException:
            time.sleep(delay)

    return data


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", default="proofwiki_raw.json")
    parser.add_argument("--delay", type=float, default=0.5)
    parser.add_argument("--limit", type=int, default=None)
    parser.add_argument("--category-url", default=DEFAULT_CATEGORY_URL)
    args = parser.parse_args()

    session = requests.Session()
    session.headers.update(
        {
            "User-Agent": "DistillationProofCollector/1.0 (+https://proofwiki.org)",
        }
    )

    links = get_category_links(session, args.category_url)
    data = scrape_all(links, delay=args.delay, limit=args.limit)

    with open(args.output, "w", encoding="utf-8") as handle:
        json.dump(data, handle, ensure_ascii=False, indent=2)


if __name__ == "__main__":
    main()