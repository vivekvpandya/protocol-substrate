use arkworks_setups::{common::setup_params, Curve};
use codec::Encode;
use frame_benchmarking::account;
use frame_support::{assert_noop, assert_ok, traits::OnInitialize};
use sp_runtime::traits::{One, Zero};
use webb_primitives::{merkle_tree::TreeInspector, AccountId, ElementTrait};

use pallet_asset_registry::AssetType;
use sp_runtime::{DispatchError, TokenError};

use crate::{mock::*, test_utils::*};

const SEED: u32 = 0;

fn hasher_params() -> Vec<u8> {
	let curve = Curve::Bn254;
	let params = setup_params::<ark_bn254::Fr>(curve, 5, 3);
	params.to_bytes()
}

fn setup_cryptography_pallets(curve: Curve) -> Vec<u8> {
	match curve {
		Curve::Bn254 => {
			let params3 = hasher_params();

			// 1. Setup The Hasher Pallet.
			assert_ok!(HasherPallet::force_set_parameters(Origin::root(), params3));
			// 2. Initialize MerkleTree pallet.
			<MerkleTree as OnInitialize<u64>>::on_initialize(1);
			// 3. Setup the VerifierPallet
			//    but to do so, we need to have a VerifyingKey
			let pk_bytes = include_bytes!(
				"../../../protocol-substrate-fixtures/mixer/bn254/x5/proving_key_uncompressed.bin"
			);
			let vk_bytes = include_bytes!(
				"../../../protocol-substrate-fixtures/mixer/bn254/x5/verifying_key.bin"
			);

			assert_ok!(VerifierPallet::force_set_parameters(Origin::root(), vk_bytes.to_vec()));

			// finally return the provingkey bytes
			pk_bytes.to_vec()
		},
		Curve::Bls381 => {
			unimplemented!()
		},
	}
}

fn setup_cryptography_pallets_for_instace2(curve: Curve) -> Vec<u8> {
	match curve {
		Curve::Bn254 => {
			let params3 = hasher_params();

			// 1. Setup The Hasher Pallet.
			assert_ok!(HasherPallet::force_set_parameters(Origin::root(), params3));
			// 2. Initialize MerkleTree pallet.
			<MerkleTree2 as OnInitialize<u64>>::on_initialize(1);
			// 3. Setup the VerifierPallet
			//    but to do so, we need to have a VerifyingKey
			let pk_bytes = include_bytes!(
				"../../../protocol-substrate-fixtures/mixer/bn254/x5/proving_key_uncompressed.bin"
			);
			let vk_bytes = include_bytes!(
				"../../../protocol-substrate-fixtures/mixer/bn254/x5/verifying_key.bin"
			);

			assert_ok!(VerifierPallet::force_set_parameters(Origin::root(), vk_bytes.to_vec()));

			// finally return the provingkey bytes
			pk_bytes.to_vec()
		},
		Curve::Bls381 => {
			unimplemented!()
		},
	}
}

fn setup_environment(curve: Curve) -> Vec<u8> {
	for account_id in [
		account::<AccountId>("", 1, SEED),
		account::<AccountId>("", 2, SEED),
		account::<AccountId>("", 3, SEED),
		account::<AccountId>("", 4, SEED),
		account::<AccountId>("", 5, SEED),
		account::<AccountId>("", 6, SEED),
	] {
		assert_ok!(Balances::set_balance(Origin::root(), account_id, 100_000_000, 0));
	}
	setup_cryptography_pallets(curve)
}

#[test]
fn should_create_new_mixer() {
	new_test_ext().execute_with(|| {
		// init hasher pallet first.
		assert_ok!(HasherPallet::force_set_parameters(Origin::root(), hasher_params()));
		// then the merkle tree.
		<MerkleTree as OnInitialize<u64>>::on_initialize(1);
		assert_ok!(Mixer::create(Origin::root(), One::one(), 3, 0));
	});
}

#[test]
fn should_be_able_to_deposit() {
	new_test_ext().execute_with(|| {
		let _ = setup_environment(Curve::Bn254);
		// init hasher pallet first.
		assert_ok!(HasherPallet::force_set_parameters(Origin::root(), hasher_params()));
		// then the merkle tree.
		<MerkleTree as OnInitialize<u64>>::on_initialize(1);
		let deposit_size = One::one();
		assert_ok!(Mixer::create(Origin::root(), deposit_size, 3, 0));
		let tree_id = MerkleTree::next_tree_id() - 1;
		let account_id = account::<AccountId>("", 1, SEED);
		let leaf = Element::from_bytes(&[1u8; 32]);
		// check the balance before the deposit.
		let balance_before = Mixer::free_balance(0, account_id.clone());
		// and we do the deposit
		assert_ok!(Mixer::deposit(Origin::signed(account_id.clone()), tree_id, leaf));
		// now we check the balance after the deposit.
		let balance_after = Mixer::free_balance(0, account_id.clone());
		// the balance should be less now with `deposit_size`
		assert_eq!(balance_after, balance_before - deposit_size);
		// now we need also to check if the state got updated.
		let tree = MerkleTree::trees(tree_id).unwrap();
		assert_eq!(tree.leaf_count, 1);
	});
}

#[test]
fn mixer_works_with_wasm_utils() {
	new_test_ext().execute_with(|| {
		let curve = Curve::Bn254;
		let pk_bytes = setup_environment(curve);
		// now let's create the mixer.
		let deposit_size = One::one();
		assert_ok!(Mixer::create(Origin::root(), deposit_size, 30, 0));
		// now with mixer created, we should setup the circuit.
		let tree_id = MerkleTree::next_tree_id() - 1;
		let sender_account_id = account::<AccountId>("", 1, SEED);
		let recipient_account_id = account::<AccountId>("", 2, SEED);
		let relayer_account_id = account::<AccountId>("", 0, SEED);
		let fee_value = 0;
		let refund_value = 0;

		// inputs
		let recipient_bytes = crate::truncate_and_pad(&recipient_account_id.encode()[..]);
		let relayer_bytes = crate::truncate_and_pad(&relayer_account_id.encode()[..]);

		let (proof_bytes, root_element, nullifier_hash_element, leaf_element) =
			setup_wasm_utils_zk_circuit(
				curve,
				recipient_bytes,
				relayer_bytes,
				pk_bytes,
				fee_value,
				refund_value,
			);

		assert_ok!(Mixer::deposit(
			Origin::signed(sender_account_id.clone()),
			tree_id,
			leaf_element,
		));
		// check the balance before the withdraw.
		let balance_before = Mixer::free_balance(0, recipient_account_id.clone());

		let mixer_tree_root = MerkleTree::get_root(tree_id).unwrap();
		assert_eq!(root_element, mixer_tree_root);

		assert_ok!(Mixer::withdraw(
			Origin::signed(sender_account_id),
			tree_id,
			proof_bytes,
			root_element,
			nullifier_hash_element,
			recipient_account_id.clone(),
			relayer_account_id,
			fee_value.into(),
			refund_value.into(),
		));
		// now we check the recipient balance again.
		let balance_after = Mixer::free_balance(0, recipient_account_id.clone());
		assert_eq!(balance_after, balance_before + deposit_size);
		// perfect
	});
}

#[test]
fn mixer_works() {
	new_test_ext().execute_with(|| {
		let curve = Curve::Bn254;
		let pk_bytes = setup_environment(curve);
		// now let's create the mixer.
		let deposit_size = One::one();
		assert_ok!(Mixer::create(Origin::root(), deposit_size, 30, 0));
		// now with mixer created, we should setup the circuit.
		let tree_id = MerkleTree::next_tree_id() - 1;
		let sender_account_id = account::<AccountId>("", 1, SEED);
		let recipient_account_id = account::<AccountId>("", 2, SEED);
		let relayer_account_id = account::<AccountId>("", 0, SEED);
		let fee_value = 0;
		let refund_value = 0;

		// inputs
		let recipient_bytes = crate::truncate_and_pad(&recipient_account_id.encode()[..]);
		let relayer_bytes = crate::truncate_and_pad(&relayer_account_id.encode()[..]);

		let (proof_bytes, root_element, nullifier_hash_element, leaf_element) = setup_zk_circuit(
			curve,
			recipient_bytes,
			relayer_bytes,
			pk_bytes,
			fee_value,
			refund_value,
		);

		assert_ok!(Mixer::deposit(
			Origin::signed(sender_account_id.clone()),
			tree_id,
			leaf_element,
		));
		// check the balance before the withdraw.
		let balance_before = Mixer::free_balance(0, recipient_account_id.clone());

		let mixer_tree_root = MerkleTree::get_root(tree_id).unwrap();
		assert_eq!(root_element, mixer_tree_root);

		assert_ok!(Mixer::withdraw(
			Origin::signed(sender_account_id),
			tree_id,
			proof_bytes,
			root_element,
			nullifier_hash_element,
			recipient_account_id.clone(),
			relayer_account_id,
			fee_value.into(),
			refund_value.into(),
		));
		// now we check the recipient balance again.
		let balance_after = Mixer::free_balance(0, recipient_account_id.clone());
		assert_eq!(balance_after, balance_before + deposit_size);
		// perfect
	});
}

#[test]
fn mixer_works_with_pallet_assets() {
	new_test_ext().execute_with(|| {
		let curve = Curve::Bn254;
		let pk_bytes = setup_cryptography_pallets_for_instace2(curve);
		// now let's create the mixer.
		let deposit_size = One::one();
		assert_ok!(Mixer2::create(Origin::root(), deposit_size, 30, 0));
		// now with mixer created, we should setup the circuit.
		let tree_id = MerkleTree2::next_tree_id() - 1;
		let sender_account_id = account::<AccountId>("", 1, SEED);
		let recipient_account_id = account::<AccountId>("", 2, SEED);
		let relayer_account_id = account::<AccountId>("", 0, SEED);
		let fee_value = 0;
		let refund_value = 0;

		// inputs
		let recipient_bytes = crate::truncate_and_pad(&recipient_account_id.encode()[..]);
		let relayer_bytes = crate::truncate_and_pad(&relayer_account_id.encode()[..]);

		let (proof_bytes, root_element, nullifier_hash_element, leaf_element) = setup_zk_circuit(
			curve,
			recipient_bytes,
			relayer_bytes,
			pk_bytes,
			fee_value,
			refund_value,
		);

		assert_ok!(Mixer2::deposit(
			Origin::signed(sender_account_id.clone()),
			tree_id,
			leaf_element,
		));
		// check the balance before the withdraw.
		let balance_before = Mixer2::free_balance(0, recipient_account_id.clone());

		let mixer_tree_root = MerkleTree2::get_root(tree_id).unwrap();
		assert_eq!(root_element, mixer_tree_root);

		assert_ok!(Mixer2::withdraw(
			Origin::signed(sender_account_id),
			tree_id,
			proof_bytes,
			root_element,
			nullifier_hash_element,
			recipient_account_id.clone(),
			relayer_account_id,
			fee_value.into(),
			refund_value.into(),
		));
		// now we check the recipient balance again.
		let balance_after = Mixer2::free_balance(0, recipient_account_id.clone());
		assert_eq!(balance_after, balance_before + deposit_size);
		// perfect
	});
}

#[test]
fn mixer_should_fail_with_when_proof_when_any_byte_is_changed_in_proof() {
	new_test_ext().execute_with(|| {
		let curve = Curve::Bn254;
		let pk_bytes = setup_environment(curve);

		let deposit_size = One::one();
		assert_ok!(Mixer::create(Origin::root(), deposit_size, 30, 0));
		// now with mixer created, we should setup the circuit.
		let tree_id = MerkleTree::next_tree_id() - 1;
		let sender_account_id = account::<AccountId>("", 1, SEED);
		let recipient_account_id = account::<AccountId>("", 2, SEED);
		let relayer_account_id = account::<AccountId>("", 0, SEED);
		let fee_value = 0;
		let refund_value = 0;

		// inputs
		let recipient_bytes = crate::truncate_and_pad(&recipient_account_id.encode()[..]);
		let relayer_bytes = crate::truncate_and_pad(&relayer_account_id.encode()[..]);

		let (mut proof_bytes, root_element, nullifier_hash_element, leaf_element) =
			setup_zk_circuit(
				curve,
				recipient_bytes,
				relayer_bytes,
				pk_bytes,
				fee_value,
				refund_value,
			);

		assert_ok!(Mixer::deposit(
			Origin::signed(sender_account_id.clone()),
			tree_id,
			leaf_element,
		));

		let mixer_tree_root = MerkleTree::get_root(tree_id).unwrap();
		assert_eq!(root_element, mixer_tree_root);

		let a = proof_bytes[0];
		let b = proof_bytes[1];
		proof_bytes[0] = b;
		proof_bytes[1] = a;

		assert_noop!(
			Mixer::withdraw(
				Origin::signed(sender_account_id),
				tree_id,
				proof_bytes,
				root_element,
				nullifier_hash_element,
				recipient_account_id,
				relayer_account_id,
				fee_value.into(),
				refund_value.into(),
			),
			crate::Error::<Test, crate::Instance1>::InvalidWithdrawProof
		);
	});
}

#[test]
fn mixer_should_fail_when_invalid_merkle_roots() {
	new_test_ext().execute_with(|| {
		let curve = Curve::Bn254;

		let pk_bytes = setup_environment(curve);

		let deposit_size = One::one();
		assert_ok!(Mixer::create(Origin::root(), deposit_size, 30, 0));
		// now with mixer created, we should setup the circuit.
		let tree_id = MerkleTree::next_tree_id() - 1;
		let sender_account_id = account::<AccountId>("", 1, SEED);
		let recipient_account_id = account::<AccountId>("", 2, SEED);
		let relayer_account_id = account::<AccountId>("", 0, SEED);
		let fee_value = 0;
		let refund_value = 0;

		// inputs
		let recipient_bytes = crate::truncate_and_pad(&recipient_account_id.encode()[..]);
		let relayer_bytes = crate::truncate_and_pad(&relayer_account_id.encode()[..]);

		let (proof_bytes, root_element, nullifier_hash_element, leaf_element) = setup_zk_circuit(
			curve,
			recipient_bytes,
			relayer_bytes,
			pk_bytes,
			fee_value,
			refund_value,
		);

		assert_ok!(Mixer::deposit(
			Origin::signed(sender_account_id.clone()),
			tree_id,
			leaf_element,
		));

		let mut root_element_bytes = root_element.to_bytes().to_vec();
		let a = root_element_bytes[0];
		let b = root_element_bytes[1];
		root_element_bytes[0] = b;
		root_element_bytes[1] = a;
		let root_element = Element::from_bytes(&root_element_bytes[..]);

		// now we start to generate the proof.
		assert_noop!(
			Mixer::withdraw(
				Origin::signed(sender_account_id),
				tree_id,
				proof_bytes,
				root_element,
				nullifier_hash_element,
				recipient_account_id,
				relayer_account_id,
				fee_value.into(),
				refund_value.into(),
			),
			crate::Error::<Test, crate::Instance1>::UnknownRoot
		);
	});
}

#[test]
fn mixer_should_fail_when_relayer_id_is_different_from_that_in_proof_generation() {
	new_test_ext().execute_with(|| {
		let curve = Curve::Bn254;
		let pk_bytes = setup_environment(curve);

		let deposit_size = One::one();
		assert_ok!(Mixer::create(Origin::root(), deposit_size, 30, 0));
		// now with mixer created, we should setup the circuit.
		let tree_id = MerkleTree::next_tree_id() - 1;
		let sender_account_id = account::<AccountId>("", 1, SEED);
		let recipient_account_id = account::<AccountId>("", 2, SEED);
		let relayer_account_id = account::<AccountId>("", 0, SEED);
		let fee_value = 0;
		let refund_value = 0;

		// inputs
		let recipient_bytes = crate::truncate_and_pad(&recipient_account_id.encode()[..]);
		let relayer_bytes = crate::truncate_and_pad(&relayer_account_id.encode()[..]);

		let (proof_bytes, root_element, nullifier_hash_element, leaf_element) = setup_zk_circuit(
			curve,
			recipient_bytes,
			relayer_bytes,
			pk_bytes,
			fee_value,
			refund_value,
		);

		assert_ok!(Mixer::deposit(
			Origin::signed(sender_account_id.clone()),
			tree_id,
			leaf_element,
		));

		let mixer_tree_root = MerkleTree::get_root(tree_id).unwrap();
		assert_eq!(root_element, mixer_tree_root);

		assert_noop!(
			Mixer::withdraw(
				Origin::signed(sender_account_id.clone()),
				tree_id,
				proof_bytes,
				root_element,
				nullifier_hash_element,
				recipient_account_id,
				sender_account_id,
				fee_value.into(),
				refund_value.into(),
			),
			crate::Error::<Test, crate::Instance1>::InvalidWithdrawProof
		);
	});
}

#[test]
fn mixer_should_fail_with_when_fee_submitted_is_changed() {
	new_test_ext().execute_with(|| {
		let curve = Curve::Bn254;
		let pk_bytes = setup_environment(curve);

		let deposit_size = One::one();
		assert_ok!(Mixer::create(Origin::root(), deposit_size, 30, 0));
		// now with mixer created, we should setup the circuit.
		let tree_id = MerkleTree::next_tree_id() - 1;
		let sender_account_id = account::<AccountId>("", 1, SEED);
		let recipient_account_id = account::<AccountId>("", 2, SEED);
		let relayer_account_id = account::<AccountId>("", 0, SEED);
		let fee_value = 0;
		let refund_value = 0;

		// inputs
		let recipient_bytes = crate::truncate_and_pad(&recipient_account_id.encode()[..]);
		let relayer_bytes = crate::truncate_and_pad(&relayer_account_id.encode()[..]);

		let (proof_bytes, root_element, nullifier_hash_element, leaf_element) = setup_zk_circuit(
			curve,
			recipient_bytes,
			relayer_bytes,
			pk_bytes,
			fee_value,
			refund_value,
		);

		assert_ok!(Mixer::deposit(
			Origin::signed(sender_account_id.clone()),
			tree_id,
			leaf_element,
		));

		let mixer_tree_root = MerkleTree::get_root(tree_id).unwrap();
		assert_eq!(root_element, mixer_tree_root);

		assert_noop!(
			Mixer::withdraw(
				Origin::signed(sender_account_id),
				tree_id,
				proof_bytes,
				root_element,
				nullifier_hash_element,
				recipient_account_id,
				relayer_account_id,
				100u128,
				refund_value.into(),
			),
			crate::Error::<Test, crate::Instance1>::InvalidWithdrawProof
		);
	});
}

#[test]
fn mixer_should_fail_with_invalid_proof_when_account_ids_are_truncated_in_reverse() {
	new_test_ext().execute_with(|| {
		let curve = Curve::Bn254;
		let pk_bytes = setup_environment(curve);

		let deposit_size = One::one();
		assert_ok!(Mixer::create(Origin::root(), deposit_size, 30, 0));
		// now with mixer created, we should setup the circuit.
		let tree_id = MerkleTree::next_tree_id() - 1;
		let sender_account_id = account::<AccountId>("", 1, SEED);
		let recipient_account_id = account::<AccountId>("", 2, SEED);
		let relayer_account_id = account::<AccountId>("", 0, SEED);
		let fee_value = 0;
		let refund_value = 0;

		// inputs
		let recipient_bytes = truncate_and_pad_reverse(&recipient_account_id.encode()[..]);
		let relayer_bytes = truncate_and_pad_reverse(&relayer_account_id.encode()[..]);

		let (proof_bytes, root_element, nullifier_hash_element, leaf_element) = setup_zk_circuit(
			curve,
			recipient_bytes,
			relayer_bytes,
			pk_bytes,
			fee_value,
			refund_value,
		);

		assert_ok!(Mixer::deposit(
			Origin::signed(sender_account_id.clone()),
			tree_id,
			leaf_element,
		));

		let mixer_tree_root = MerkleTree::get_root(tree_id).unwrap();
		assert_eq!(root_element, mixer_tree_root);

		assert_noop!(
			Mixer::withdraw(
				Origin::signed(sender_account_id),
				tree_id,
				proof_bytes,
				root_element,
				nullifier_hash_element,
				recipient_account_id,
				relayer_account_id,
				fee_value.into(),
				refund_value.into(),
			),
			crate::Error::<Test, crate::Instance1>::InvalidWithdrawProof
		);
	});
}

#[test]
fn double_spending_should_fail() {
	new_test_ext().execute_with(|| {
		let curve = Curve::Bn254;
		let pk_bytes = setup_environment(curve);

		let deposit_size = One::one();
		assert_ok!(Mixer::create(Origin::root(), deposit_size, 30, 0));
		// now with mixer created, we should setup the circuit.
		let tree_id = MerkleTree::next_tree_id() - 1;
		let sender_account_id = account::<AccountId>("", 1, SEED);
		let recipient_account_id = account::<AccountId>("", 2, SEED);
		let relayer_account_id = account::<AccountId>("", 0, SEED);
		let fee_value = 0;
		let refund_value = 0;

		// inputs
		let recipient_bytes = crate::truncate_and_pad(&recipient_account_id.encode()[..]);
		let relayer_bytes = crate::truncate_and_pad(&relayer_account_id.encode()[..]);

		let (proof_bytes, root_element, nullifier_hash_element, leaf_element) = setup_zk_circuit(
			curve,
			recipient_bytes,
			relayer_bytes,
			pk_bytes,
			fee_value,
			refund_value,
		);

		assert_ok!(Mixer::deposit(
			Origin::signed(sender_account_id.clone()),
			tree_id,
			leaf_element,
		));

		let mixer_tree_root = MerkleTree::get_root(tree_id).unwrap();
		assert_eq!(root_element, mixer_tree_root);

		let balance_before = Mixer::free_balance(0, recipient_account_id.clone());

		assert_ok!(Mixer::withdraw(
			Origin::signed(sender_account_id.clone()),
			tree_id,
			proof_bytes.clone(),
			root_element,
			nullifier_hash_element,
			recipient_account_id.clone(),
			relayer_account_id.clone(),
			fee_value.into(),
			refund_value.into(),
		));
		// now we check the recipient balance again.
		let balance_after = Mixer::free_balance(0, recipient_account_id.clone());
		assert_eq!(balance_after, balance_before + deposit_size);
		// perfect

		assert_noop!(
			Mixer::withdraw(
				Origin::signed(sender_account_id),
				tree_id,
				proof_bytes,
				root_element,
				nullifier_hash_element,
				recipient_account_id,
				relayer_account_id,
				fee_value.into(),
				refund_value.into(),
			),
			crate::Error::<Test, crate::Instance1>::AlreadyRevealedNullifier
		);
	});
}

#[test]
fn deposit_with_non_native_asset_should_work() {
	new_test_ext().execute_with(|| {
		// create an Asset first
		assert_ok!(
			AssetRegistry::get_or_create_asset(
				String::from("ETH").into(),
				AssetType::Token,
				Zero::zero(),
			),
			1
		);

		let currency_id = AssetRegistry::next_asset_id() - 1;

		let curve = Curve::Bn254;
		let pk_bytes = setup_environment(curve);

		let deposit_size = One::one();
		assert_ok!(Mixer::create(Origin::root(), deposit_size, 30, currency_id));
		// now with mixer created, we should setup the circuit.
		let tree_id = MerkleTree::next_tree_id() - 1;
		let sender_account_id = account::<AccountId>("", 1, SEED);
		let recipient_account_id = account::<AccountId>("", 2, SEED);
		let relayer_account_id = account::<AccountId>("", 0, SEED);
		let fee_value = 0;
		let refund_value = 0;

		// inputs
		let recipient_bytes = crate::truncate_and_pad(&recipient_account_id.encode()[..]);
		let relayer_bytes = crate::truncate_and_pad(&relayer_account_id.encode()[..]);

		let (_, _, _, leaf_element) = setup_zk_circuit(
			curve,
			recipient_bytes,
			relayer_bytes,
			pk_bytes,
			fee_value,
			refund_value,
		);
		// check my balance first, before sending the deposit
		let initial_balance = 0_u128;
		assert_eq!(Mixer::free_balance(currency_id, sender_account_id.clone()), initial_balance);
		// now we add some balance
		let new_balance = 100;
		assert_ok!(Mixer::mint_into(currency_id, sender_account_id.clone(), new_balance,));
		// now we do check the balance again, it should be updated
		assert_eq!(
			Mixer::free_balance(currency_id, sender_account_id.clone()),
			(initial_balance + new_balance) as _
		);
		// and then we do the deposit
		assert_ok!(Mixer::deposit(
			Origin::signed(sender_account_id.clone()),
			tree_id,
			leaf_element,
		));
		assert_eq!(
			Mixer::free_balance(currency_id, sender_account_id),
			(initial_balance + new_balance - deposit_size) as _
		);
	});
}

#[test]
fn deposit_with_non_native_asset_works_with_pallet_assets() {
	new_test_ext().execute_with(|| {
		let currency_id = 1; // as added in GenesisConfig for pallet_assets

		let curve = Curve::Bn254;
		let pk_bytes = setup_cryptography_pallets_for_instace2(curve);

		let deposit_size = One::one();
		assert_ok!(Mixer2::create(Origin::root(), deposit_size, 30, currency_id));
		// now with mixer created, we should setup the circuit.
		let tree_id = MerkleTree2::next_tree_id() - 1;
		let sender_account_id = account::<AccountId>("", 1, SEED);
		let recipient_account_id = account::<AccountId>("", 2, SEED);
		let relayer_account_id = account::<AccountId>("", 0, SEED);
		let fee_value = 0;
		let refund_value = 0;

		// inputs
		let recipient_bytes = crate::truncate_and_pad(&recipient_account_id.encode()[..]);
		let relayer_bytes = crate::truncate_and_pad(&relayer_account_id.encode()[..]);

		let (_, _, _, leaf_element) = setup_zk_circuit(
			curve,
			recipient_bytes,
			relayer_bytes,
			pk_bytes,
			fee_value,
			refund_value,
		);
		// check my balance first, before sending the deposit
		let initial_balance = 0_u128;
		assert_eq!(Mixer2::free_balance(currency_id, sender_account_id.clone()), initial_balance);
		// now we add some balance
		let new_balance = 100;
		assert_ok!(Mixer2::mint_into(currency_id, sender_account_id.clone(), new_balance,));
		// now we do check the balance again, it should be updated
		assert_eq!(
			Mixer2::free_balance(currency_id, sender_account_id.clone()),
			(initial_balance + new_balance) as _
		);
		// and then we do the deposit
		assert_ok!(Mixer2::deposit(
			Origin::signed(sender_account_id.clone()),
			tree_id,
			leaf_element,
		));
		// our balance should be updated again
		assert_eq!(
			Mixer2::free_balance(currency_id, sender_account_id),
			(initial_balance + new_balance - deposit_size) as _
		);
	});
}

#[test]
fn mint_into_with_unknown_asset_does_not_works_with_pallet_assets() {
	new_test_ext().execute_with(|| {
		let currency_id = 2; // no asset with id = 2 has been added to pallet_assets yet.
		let sender_account_id = account::<AccountId>("", 1, SEED);
		let new_balance = 100;
		assert_noop!(
			Mixer2::mint_into(currency_id, sender_account_id.clone(), new_balance,),
			DispatchError::Token(TokenError::UnknownAsset)
		);
	});
}

#[test]
fn deposit_with_insufficient_balance_does_not_work_with_pallet_assets() {
	new_test_ext().execute_with(|| {
		let currency_id = 1; // as added in GenesisConfig for pallet_assets

		let curve = Curve::Bn254;
		let pk_bytes = setup_cryptography_pallets_for_instace2(curve);

		let deposit_size = 1000;
		assert_ok!(Mixer2::create(Origin::root(), deposit_size, 30, currency_id));
		// now with mixer created, we should setup the circuit.
		let tree_id = MerkleTree2::next_tree_id() - 1;
		let sender_account_id = account::<AccountId>("", 1, SEED);
		let recipient_account_id = account::<AccountId>("", 2, SEED);
		let relayer_account_id = account::<AccountId>("", 0, SEED);
		let fee_value = 0;
		let refund_value = 0;

		// inputs
		let recipient_bytes = crate::truncate_and_pad(&recipient_account_id.encode()[..]);
		let relayer_bytes = crate::truncate_and_pad(&relayer_account_id.encode()[..]);

		let (_, _, _, leaf_element) = setup_zk_circuit(
			curve,
			recipient_bytes,
			relayer_bytes,
			pk_bytes,
			fee_value,
			refund_value,
		);
		// check my balance first, before sending the deposit
		let initial_balance = 0_u128;
		assert_eq!(Mixer2::free_balance(currency_id, sender_account_id.clone()), initial_balance);
		// now we add some balance
		let new_balance = 100;
		assert_ok!(Mixer2::mint_into(currency_id, sender_account_id.clone(), new_balance,));
		// now we do check the balance again, it should be updated
		assert_eq!(
			Mixer2::free_balance(currency_id, sender_account_id.clone()),
			(initial_balance + new_balance) as _
		);
		// and then we do the deposit
		assert_noop!(
			Mixer2::deposit(Origin::signed(sender_account_id.clone()), tree_id, leaf_element,),
			pallet_assets::Error::<Test>::BalanceLow
		);
	});
}
