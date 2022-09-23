#[test]
fn test_ln() {
    use crate::utils::ln_without_floats;

    assert_eq!(ln_without_floats(1), 0);
    assert_eq!(ln_without_floats(2), 0);
    assert_eq!(ln_without_floats(3), 1);
    assert_eq!(ln_without_floats(30), 3);
    assert_eq!(ln_without_floats(100), 4);
}
