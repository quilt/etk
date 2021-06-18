use etk_4byte::reverse_selector;

#[test]
fn set_custodian() {
    assert_eq!(reverse_selector(0x403f3731), &["setCustodian(address)"],);
}
