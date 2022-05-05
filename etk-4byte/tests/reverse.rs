use etk_4byte::reverse_selector;

#[test]
fn set_custodian() {
    let selectors: Vec<_> = reverse_selector(0x403f3731).collect();
    assert_eq!(selectors, &["setCustodian(address)"],);
}
