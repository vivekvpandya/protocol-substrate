use crate::{mock::*, test_utils::*};
use ark_ff::{BigInteger, FromBytes, PrimeField};
use ark_serialize::CanonicalSerialize;
use ark_std::{fs::canonicalize, str::FromStr};
use arkworks_circuits::{prelude::ark_groth16::ProvingKey, setup::common::PoseidonCRH_x5_5};
use arkworks_gadgets::leaf::mixer::{MixerLeaf, Private};
use arkworks_utils::utils::common::{setup_params_x5_3, setup_params_x5_5, Curve};
use codec::Encode;
use darkwebb_primitives::{merkle_tree::TreeInspector, AccountId, ElementTrait};
use frame_benchmarking::account;
use frame_support::{assert_err, assert_ok, traits::OnInitialize};
use orml_traits::MultiCurrency;
use pallet_asset_registry::AssetType;
use sp_runtime::traits::{One, Zero};
use wasm_utils::{
	note,
	note::NoteBuilder,
	proof::{ZKProof, ZkProofBuilder},
	types,
};
type Bn254Fr = ark_bn254::Fr;

const SEED: u32 = 0;

fn hasher_params() -> Vec<u8> {
	let curve = Curve::Bn254;
	let params = setup_params_x5_3::<ark_bn254::Fr>(curve);
	params.to_bytes()
}

fn setup_environment(curve: Curve) -> Vec<u8> {
	let params = match curve {
		Curve::Bn254 => get_hash_params::<ark_bn254::Fr>(curve),
		Curve::Bls381 => get_hash_params::<ark_bls12_381::Fr>(curve),
	};
	// 1. Setup The Hasher Pallet.
	assert_ok!(HasherPallet::force_set_parameters(Origin::root(), params.0));
	// 2. Initialize MerkleTree pallet.
	<MerkleTree as OnInitialize<u64>>::on_initialize(1);
	// 3. Setup the VerifierPallet
	//    but to do so, we need to have a VerifyingKey
	let mut verifier_key_bytes = Vec::new();
	let mut proving_key_bytes = Vec::new();

	get_keys(curve, &mut proving_key_bytes, &mut verifier_key_bytes);

	assert_ok!(VerifierPallet::force_set_parameters(Origin::root(), verifier_key_bytes));

	// finally return the provingkey bytes
	proving_key_bytes
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
		let balance_before = Balances::free_balance(account_id.clone());
		// and we do the deposit
		assert_ok!(Mixer::deposit(Origin::signed(account_id.clone()), tree_id, leaf));
		// now we check the balance after the deposit.
		let balance_after = Balances::free_balance(account_id);
		// the balance should be less now with `deposit_size`
		assert_eq!(balance_after, balance_before - deposit_size);
		// now we need also to check if the state got updated.
		let tree = MerkleTree::trees(tree_id);
		assert_eq!(tree.leaf_count, 1);
	});
}
#[test]
fn should_be_able_to_change_the_maintainer() {
	new_test_ext().execute_with(|| {
		assert_ok!(Mixer::create(Origin::root(), One::one(), 3, 0));
		let default_maintainer_account_id = AccountId::default();
		let current_maintainer_account_id = Mixer::maintainer();
		assert_eq!(current_maintainer_account_id, default_maintainer_account_id);
		let new_maintainer_account_id = account::<AccountId>("", 1, SEED);
		assert_ok!(Mixer::force_set_maintainer(
			Origin::root(),
			new_maintainer_account_id.clone()
		));
		let current_maintainer_account_id = Mixer::maintainer();
		assert_eq!(current_maintainer_account_id, new_maintainer_account_id);
	});
}
#[test]
fn encoding_as_js() {
	// account
	let account_id = AccountId::from_str("jn5LuB5d51srpmZqiBNgWu11C6AeVxEygggjWsifcG1myqr").unwrap();
	let account_id_hex = hex::encode(account_id.encode());
	assert_eq!(
		account_id_hex,
		String::from("644277e80e74baf70c59aeaa038b9e95b400377d1fd09c87a6f8071bce185129")
	)
}
#[test]
fn mixer_works() {
	use ark_serialize::{CanonicalDeserialize, CanonicalSerialize};

	new_test_ext().execute_with(|| {
		let curve = Curve::Bn254;
		let pk_bytes = setup_environment(curve);
		let pk = ProvingKey::<ark_bn254::Bn254>::deserialize(&*pk_bytes).unwrap();
		let mut uncompressed_key = vec![];
		CanonicalSerialize::serialize_uncompressed(&pk, &mut uncompressed_key);

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
		// let (proof_bytes, roots_element, nullifier_hash_element, leaf_element, leaf_private) = setup_zk_circuit(
		// 	curve,
		// 	recipient_bytes.clone(),
		// 	relayer_bytes.clone(),
		// 	pk_bytes.clone(),
		// 	fee_value,
		// 	refund_value,
		// );

		let secr = hex::decode("1f183415fdc7512999283cffbed2d498f4f9910ead667d588bb8d4fee253f70bd022e5404322b738a5a7720787720805e397a5a7830798be88995880140e8001").unwrap();
		let secret = &secr[..32];
		let nullifier = &secr[32..64];

		let secret_f = Bn254Fr::from_le_bytes_mod_order(secret);
		let nullifier_f = Bn254Fr::from_le_bytes_mod_order(nullifier);

		let leaf_private = Private::new(secret_f, nullifier_f);
		// let params3 = setup_params_x5_3::<ark_bn254::Fr>(curve);
		let params5 = setup_params_x5_5::<ark_bn254::Fr>(curve);
		let leaf = MixerLeaf::<Bn254Fr, PoseidonCRH_x5_5<Bn254Fr>>::create_leaf(&leaf_private, &params5).unwrap();
		let nullifier_hash = MixerLeaf::<Bn254Fr, PoseidonCRH_x5_5<Bn254Fr>>::create_nullifier(&leaf_private, &params5).unwrap();

		let leaf_element = Element::from_bytes(&leaf.into_repr().to_bytes_le());

		let nullifier_hash_element = Element::from_bytes(&nullifier_hash.into_repr().to_bytes_le());

		let root_element = Element::from_bytes(
			&hex::decode("fe409577fc56c38c5b8582d09e0ffc10653f4e3439e686207838a7284fa69d10").unwrap(),
		);
		let roots_element = vec![root_element];

		// wasm-utils
		let mut note_builder = NoteBuilder::default();
		note_builder.backend = types::Backend::Arkworks;
		note_builder.curve = types::Curve::Bn254;
		note_builder.width = "3".to_string();
		note_builder.exponentiation = "5".to_string();
		note_builder.amount = "1".to_string();
		note_builder.hash_function = types::HashFunction::Poseidon;
		note_builder.secrets = Some(secr.clone());
		let deposit_note = note_builder.generate_note().unwrap();

		// Making the proof
		let mut proof_builder = ZkProofBuilder::new();
		let mut leaf_slice = [0u8; 32];
		leaf_slice.copy_from_slice(&leaf_element.to_vec()[..]);
		proof_builder.set_leaves(&vec![leaf_slice]);
		proof_builder.set_note(deposit_note);
		proof_builder.set_fee(fee_value);
		proof_builder.set_refund(refund_value);
		proof_builder.set_recipient(&recipient_account_id.encode()[..]);
		proof_builder.set_relayer(&relayer_account_id.encode()[..]);
		proof_builder.set_leaf_index(0);
		proof_builder.set_proving_key(&uncompressed_key);
		let proof = proof_builder.build();
		let mut proof_bytes_wasm = Vec::new();
		let root_meta = match proof {
			ZKProof::Bls12_381(proof, proof_meta) => {
				CanonicalSerialize::serialize(&proof, &mut proof_bytes_wasm).unwrap();
				proof_meta
			}
			ZKProof::Bn254(proof, proof_meta) => {
				CanonicalSerialize::serialize(&proof, &mut proof_bytes_wasm).unwrap();
				proof_meta
			}
		};
		// same root
		assert_eq!(hex::encode(&roots_element[0].to_bytes()), hex::encode(&root_meta.root));
		// same nullifier
		assert_eq!(
			hex::encode(&nullifier_hash_element.to_bytes()),
			hex::encode(root_meta.nullified_hash.clone())
		);

		// assert_eq!(hex::encode(&proof_bytes), hex::encode(&proof_bytes_wasm));
		assert_ok!(Mixer::deposit(
			Origin::signed(sender_account_id.clone()),
			tree_id,
			leaf_element,
		));
		// check the balance before the withdraw.
		let balance_before = Balances::free_balance(recipient_account_id.clone());

		let mixer_tree_root = MerkleTree::get_root(tree_id).unwrap();
		assert_eq!(roots_element[0], mixer_tree_root);
		assert_ok!(Mixer::withdraw(
			Origin::signed(sender_account_id),
			tree_id,
			proof_bytes_wasm,
			Element::from_bytes(root_meta.root.as_slice()),
			Element::from_bytes(root_meta.nullified_hash.as_slice()),
			recipient_account_id.clone(),
			relayer_account_id,
			fee_value.into(),
			refund_value.into(),
		));
		// now we check the recipient balance again.
		let balance_after = Balances::free_balance(recipient_account_id);
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

		let (mut proof_bytes, roots_element, nullifier_hash_element, leaf_element, ..) =
			setup_zk_circuit(curve, recipient_bytes, relayer_bytes, pk_bytes, fee_value, refund_value);

		assert_ok!(Mixer::deposit(
			Origin::signed(sender_account_id.clone()),
			tree_id,
			leaf_element,
		));

		let root_element = roots_element[0];
		let mixer_tree_root = MerkleTree::get_root(tree_id).unwrap();
		assert_eq!(root_element, mixer_tree_root);

		let a = proof_bytes[0];
		let b = proof_bytes[1];
		proof_bytes[0] = b;
		proof_bytes[1] = a;

		assert_err!(
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
			crate::Error::<Test>::InvalidWithdrawProof
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

		let (proof_bytes, roots_element, nullifier_hash_element, leaf_element, ..) =
			setup_zk_circuit(curve, recipient_bytes, relayer_bytes, pk_bytes, fee_value, refund_value);

		assert_ok!(Mixer::deposit(
			Origin::signed(sender_account_id.clone()),
			tree_id,
			leaf_element,
		));

		let mut root_element_bytes = roots_element[0].to_bytes().to_vec();
		let a = root_element_bytes[0];
		let b = root_element_bytes[1];
		root_element_bytes[0] = b;
		root_element_bytes[1] = a;
		let root_element = Element::from_bytes(&root_element_bytes[..]);

		// now we start to generate the proof.
		assert_err!(
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
			crate::Error::<Test>::UnknownRoot
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

		let (proof_bytes, roots_element, nullifier_hash_element, leaf_element, ..) =
			setup_zk_circuit(curve, recipient_bytes, relayer_bytes, pk_bytes, fee_value, refund_value);

		assert_ok!(Mixer::deposit(
			Origin::signed(sender_account_id.clone()),
			tree_id,
			leaf_element,
		));

		let root_element = roots_element[0];
		let mixer_tree_root = MerkleTree::get_root(tree_id).unwrap();
		assert_eq!(root_element, mixer_tree_root);

		assert_err!(
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
			crate::Error::<Test>::InvalidWithdrawProof
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

		let (proof_bytes, roots_element, nullifier_hash_element, leaf_element, ..) =
			setup_zk_circuit(curve, recipient_bytes, relayer_bytes, pk_bytes, fee_value, refund_value);

		assert_ok!(Mixer::deposit(
			Origin::signed(sender_account_id.clone()),
			tree_id,
			leaf_element,
		));

		let root_element = roots_element[0];
		let mixer_tree_root = MerkleTree::get_root(tree_id).unwrap();
		assert_eq!(root_element, mixer_tree_root);

		assert_err!(
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
			crate::Error::<Test>::InvalidWithdrawProof
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

		let (proof_bytes, roots_element, nullifier_hash_element, leaf_element, ..) =
			setup_zk_circuit(curve, recipient_bytes, relayer_bytes, pk_bytes, fee_value, refund_value);

		assert_ok!(Mixer::deposit(
			Origin::signed(sender_account_id.clone()),
			tree_id,
			leaf_element,
		));

		let root_element = roots_element[0];
		let mixer_tree_root = MerkleTree::get_root(tree_id).unwrap();
		assert_eq!(root_element, mixer_tree_root);

		assert_err!(
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
			crate::Error::<Test>::InvalidWithdrawProof
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

		let (proof_bytes, roots_element, nullifier_hash_element, leaf_element, ..) =
			setup_zk_circuit(curve, recipient_bytes, relayer_bytes, pk_bytes, fee_value, refund_value);

		assert_ok!(Mixer::deposit(
			Origin::signed(sender_account_id.clone()),
			tree_id,
			leaf_element,
		));

		let root_element = roots_element[0];
		let mixer_tree_root = MerkleTree::get_root(tree_id).unwrap();
		assert_eq!(root_element, mixer_tree_root);

		let balance_before = Balances::free_balance(recipient_account_id.clone());

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
		let balance_after = Balances::free_balance(recipient_account_id.clone());
		assert_eq!(balance_after, balance_before + deposit_size);
		// perfect

		assert_err!(
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
			crate::Error::<Test>::AlreadyRevealedNullifier
		);
	});
}

#[test]
fn deposit_with_non_native_asset_should_work() {
	new_test_ext().execute_with(|| {
		// create an Asset first
		assert_ok!(
			AssetRegistry::get_or_create_asset(String::from("ETH").into(), AssetType::Token, Zero::zero()),
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

		let (_, _, _, leaf_element, ..) =
			setup_zk_circuit(curve, recipient_bytes, relayer_bytes, pk_bytes, fee_value, refund_value);
		// check my balance first, before sending the deposit
		assert_eq!(Currencies::free_balance(currency_id, &sender_account_id), Zero::zero());
		// now we add some balance
		let new_balance = 100;
		assert_ok!(Currencies::update_balance(
			Origin::root(),
			sender_account_id.clone(),
			currency_id,
			new_balance,
		));
		// now we do check the balance again, it should be updated
		assert_eq!(
			Currencies::free_balance(currency_id, &sender_account_id),
			new_balance as _
		);
		// and then we do the deposit
		assert_ok!(Mixer::deposit(
			Origin::signed(sender_account_id.clone()),
			tree_id,
			leaf_element,
		));
		// our balance should be updated again
		assert_eq!(
			Currencies::free_balance(currency_id, &sender_account_id),
			(new_balance - deposit_size as i128) as _
		);
	});
}
