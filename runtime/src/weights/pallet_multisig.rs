//! Autogenerated weights for pallet_multisig
//!
//! THIS FILE WAS AUTO-GENERATED USING THE SUBSTRATE BENCHMARK CLI VERSION 3.0.0
//! DATE: 2021-05-31, STEPS: `[50, ]`, REPEAT: 20, LOW RANGE: `[]`, HIGH RANGE:
//! `[]` EXECUTION: Some(Wasm), WASM-EXECUTION: Compiled, CHAIN:
//! Some("statemine-dev"), DB CACHE: 128

// Executed Command:
// ./target/release/statemint
// benchmark
// --chain=statemine-dev
// --execution=wasm
// --wasm-execution=compiled
// --pallet=pallet_multisig
// --extrinsic=*
// --steps=50
// --repeat=20
// --raw
// --output=./runtime/statemine/src/weights/

#![allow(unused_parens)]
#![allow(unused_imports)]

use frame_support::{traits::Get, weights::Weight};
use sp_std::marker::PhantomData;

/// Weight functions for pallet_multisig.
pub struct WeightInfo<T>(PhantomData<T>);
impl<T: frame_system::Config> pallet_multisig::WeightInfo for WeightInfo<T> {
	fn as_multi_threshold_1(z: u32) -> Weight {
		(15_911_000 as Weight)
			// Standard Error: 0
			.saturating_add((1_000 as Weight).saturating_mul(z as Weight))
	}

	fn as_multi_create(s: u32, z: u32) -> Weight {
		(55_326_000 as Weight)
			// Standard Error: 0
			.saturating_add((133_000 as Weight).saturating_mul(s as Weight))
			// Standard Error: 0
			.saturating_add((1_000 as Weight).saturating_mul(z as Weight))
			.saturating_add(T::DbWeight::get().reads(2 as Weight))
			.saturating_add(T::DbWeight::get().writes(1 as Weight))
	}

	fn as_multi_create_store(s: u32, z: u32) -> Weight {
		(62_423_000 as Weight)
			// Standard Error: 0
			.saturating_add((133_000 as Weight).saturating_mul(s as Weight))
			// Standard Error: 0
			.saturating_add((3_000 as Weight).saturating_mul(z as Weight))
			.saturating_add(T::DbWeight::get().reads(3 as Weight))
			.saturating_add(T::DbWeight::get().writes(2 as Weight))
	}

	fn as_multi_approve(s: u32, z: u32) -> Weight {
		(32_430_000 as Weight)
			// Standard Error: 0
			.saturating_add((148_000 as Weight).saturating_mul(s as Weight))
			// Standard Error: 0
			.saturating_add((1_000 as Weight).saturating_mul(z as Weight))
			.saturating_add(T::DbWeight::get().reads(1 as Weight))
			.saturating_add(T::DbWeight::get().writes(1 as Weight))
	}

	fn as_multi_approve_store(s: u32, z: u32) -> Weight {
		(59_789_000 as Weight)
			// Standard Error: 0
			.saturating_add((165_000 as Weight).saturating_mul(s as Weight))
			// Standard Error: 0
			.saturating_add((3_000 as Weight).saturating_mul(z as Weight))
			.saturating_add(T::DbWeight::get().reads(2 as Weight))
			.saturating_add(T::DbWeight::get().writes(2 as Weight))
	}

	fn as_multi_complete(s: u32, z: u32) -> Weight {
		(80_926_000 as Weight)
			// Standard Error: 0
			.saturating_add((276_000 as Weight).saturating_mul(s as Weight))
			// Standard Error: 0
			.saturating_add((5_000 as Weight).saturating_mul(z as Weight))
			.saturating_add(T::DbWeight::get().reads(3 as Weight))
			.saturating_add(T::DbWeight::get().writes(3 as Weight))
	}

	fn approve_as_multi_create(s: u32) -> Weight {
		(54_860_000 as Weight)
			// Standard Error: 0
			.saturating_add((134_000 as Weight).saturating_mul(s as Weight))
			.saturating_add(T::DbWeight::get().reads(2 as Weight))
			.saturating_add(T::DbWeight::get().writes(1 as Weight))
	}

	fn approve_as_multi_approve(s: u32) -> Weight {
		(31_924_000 as Weight)
			// Standard Error: 0
			.saturating_add((154_000 as Weight).saturating_mul(s as Weight))
			.saturating_add(T::DbWeight::get().reads(1 as Weight))
			.saturating_add(T::DbWeight::get().writes(1 as Weight))
	}

	fn approve_as_multi_complete(s: u32) -> Weight {
		(154_001_000 as Weight)
			// Standard Error: 0
			.saturating_add((281_000 as Weight).saturating_mul(s as Weight))
			.saturating_add(T::DbWeight::get().reads(3 as Weight))
			.saturating_add(T::DbWeight::get().writes(3 as Weight))
	}

	fn cancel_as_multi(s: u32) -> Weight {
		(103_770_000 as Weight)
			// Standard Error: 0
			.saturating_add((130_000 as Weight).saturating_mul(s as Weight))
			.saturating_add(T::DbWeight::get().reads(2 as Weight))
			.saturating_add(T::DbWeight::get().writes(2 as Weight))
	}
}
