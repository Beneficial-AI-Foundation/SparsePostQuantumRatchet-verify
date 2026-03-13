# Aeneas extraction status

## Modules that extract cleanly (no changes needed)

- `spqr::util`
- `spqr::serialize`

## Modules that extract cleanly (with modifications)

### `spqr::encoding`

Excluded (platform-specific, not needed for verification):
- `encoding::gf::check_accelerated` -- excluded
- `encoding::gf::accelerated` -- excluded

Marked as opaque:
- `encoding::gf::mul2_u16` -- opaque
- `encoding::gf::MulAssign<&GF16> for GF16` -- opaque
- `encoding::polynomial::PolyDecoder::decoded_message` -- opaque

Modified source (replaced iterator combinators / early returns with index loops):
- `encoding::gf::GF16::div_impl` -- avoid opaque tuple return
- `encoding::polynomial::Poly::compute_at` -- zip to index loop
- `encoding::polynomial::Poly::lagrange_sum` -- zip to index loop
- `encoding::polynomial::Poly::from_complete_points` -- map/collect to push loop
- `encoding::polynomial::Poly::deserialize` -- chunks_exact to while loop
- `encoding::polynomial::PolyEncoder::from_pb` -- flatten if/else, remove closure
- `encoding::polynomial::PolyDecoder::from_pb` -- hoist validation before loop

## Modules not yet extracted

- `spqr::kdf` -- Charon hangs
- `spqr::chain` -- Charon hangs
- `spqr::authenticator` -- Charon hangs
- `spqr::v1` -- Charon hangs
- `spqr::proto` -- Charon hangs
- `spqr::incremental_mlkem768` -- Charon OK, Aeneas errors (not yet investigated)
