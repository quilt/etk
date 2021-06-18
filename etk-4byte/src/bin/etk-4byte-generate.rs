use reqwest::{Error, Url};

use serde::{Deserialize, Serialize};

use std::collections::{BTreeMap, BTreeSet};

#[derive(Debug, Serialize, Deserialize)]
struct Signature {
    text_signature: String,
    hex_signature: String,
}

impl Signature {
    fn selector(&self) -> u32 {
        let strip = self.hex_signature.strip_prefix("0x").unwrap();
        u32::from_str_radix(strip, 16).unwrap()
    }
}

#[derive(Debug, Serialize, Deserialize)]
struct Page<T> {
    next: Option<String>,
    previous: Option<String>,
    count: usize,
    results: Vec<T>,
}

impl Page<Signature> {
    fn insert_into(&mut self, map: &mut BTreeMap<u32, BTreeSet<String>>) {
        for sig in self.results.drain(..) {
            if sig.text_signature.contains(' ') || sig.text_signature.contains('#') {
                panic!("invalid character");
            }

            map.entry(sig.selector())
                .or_default()
                .insert(sig.text_signature);
        }
    }
}

async fn fetch(path: &str) -> Result<Page<Signature>, Error> {
    let base = Url::parse("https://www.4byte.directory/").unwrap();
    let url = base.join(path).unwrap();
    eprintln!("Fetching `{}`...", url);
    reqwest::get(url).await?.json().await
}

async fn fetch_page(page: usize) -> Result<Page<Signature>, Error> {
    fetch(&format!("/api/v1/signatures/?page={}", page)).await
}

#[tokio::main(flavor = "current_thread")]
async fn main() -> Result<(), Error> {
    let mut map: BTreeMap<u32, BTreeSet<String>> = BTreeMap::new();

    let mut current = fetch_page(1).await?;
    current.insert_into(&mut map);

    while let Some(ref next) = current.next.take() {
        current = fetch(next).await?;
        current.insert_into(&mut map);
    }

    for (selector, signatures) in map {
        let signatures: Vec<_> = signatures.into_iter().collect();
        println!("{} {}", selector, signatures.join(" "));
    }

    Ok(())
}
