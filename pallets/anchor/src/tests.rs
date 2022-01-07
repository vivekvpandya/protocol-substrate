use std::{convert::TryInto, path::Path};

use ark_bn254::{Fr as Bn254Fr, Bn254};
use ark_ff::{BigInteger, PrimeField};
use arkworks_circuits::setup::common::setup_keys;
use arkworks_utils::utils::common::{Curve, setup_params_x5_3, setup_params_x5_4};
use darkwebb_primitives::{merkle_tree::TreeInspector, AccountId, ElementTrait};

use codec::Encode;

use frame_benchmarking::account;
use frame_support::{assert_err, assert_ok, error::BadOrigin, traits::OnInitialize};
use pallet_asset_registry::AssetType;

use crate::{mock::*, test_utils::*};

const SEED: u32 = 0;
const TREE_DEPTH: usize = 30;
const M: usize = 2;
const DEPOSIT_SIZE: u128 = 10_000;

fn setup_environment(curve: Curve) -> Vec<u8> {
	match curve {
		Curve::Bn254 => {
			let params3 = setup_params_x5_3::<Bn254Fr>(curve);
			let params4 = setup_params_x5_4::<Bn254Fr>(curve);

			// 1. Setup The Hasher Pallet.
			assert_ok!(HasherPallet::force_set_parameters(Origin::root(), params3.to_bytes()));
			// 2. Initialize MerkleTree pallet.
			<MerkleTree as OnInitialize<u64>>::on_initialize(1);
			// 3. Setup the VerifierPallet
			//    but to do so, we need to have a VerifyingKey
			let (pk_bytes, vk_bytes) = if Path::new("../../protocol-substrate-fixtures/fixed-anchor/bn254/x5_4_leaf/proving_key.bin").exists() {
				let (pk, vk) = (
					std::fs::read("../../protocol-substrate-fixtures/fixed-anchor/bn254/x5_4_leaf/proving_key.bin").expect("Unable to read file").to_vec(),
					std::fs::read("../../protocol-substrate-fixtures/fixed-anchor/bn254/x5_4_leaf/verifying_key.bin").expect("Unable to read file").to_vec()
				);
				(pk.to_vec(), vk.to_vec())
			} else {
				let rng = &mut ark_std::test_rng();
				let anchor_setup = AnchorSetup30_2::new(params3, params4);
				let (circuit, .., public_inputs) = anchor_setup.setup_random_circuit(rng).unwrap();
				let (pk, vk) = setup_keys::<Bn254, _, _>(circuit.clone(), rng).unwrap();
				std::fs::write("../../protocol-substrate-fixtures/fixed-anchor/bn254/x5_4_leaf/proving_key.bin", &pk).expect("Unable to write file");
				std::fs::write("../../protocol-substrate-fixtures/fixed-anchor/bn254/x5_4_leaf/verifying_key.bin", &vk).expect("Unable to write file");
				(pk, vk)
			};

			assert_ok!(VerifierPallet::force_set_parameters(Origin::root(), vk_bytes.to_vec()));

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

			// finally return the provingkey bytes
			pk_bytes.to_vec()
		}
		Curve::Bls381 => {
			unimplemented!()
		}
	}
}

#[test]
fn should_create_new_anchor() {
	new_test_ext().execute_with(|| {
		setup_environment(Curve::Bn254);
		let max_edges = M as _;
		let depth = TREE_DEPTH as u8;
		let asset_id = 0;

		assert_ok!(Anchor::create(Origin::root(), DEPOSIT_SIZE, max_edges, depth, asset_id));

		let tree_id = MerkleTree::next_tree_id() - 1;
		crate::mock::assert_last_event::<Test>(crate::Event::<Test>::AnchorCreation { tree_id }.into());
	});
}

#[test]
fn should_fail_to_create_new_anchor_if_not_root() {
	new_test_ext().execute_with(|| {
		setup_environment(Curve::Bn254);
		let max_edges = M as _;
		let depth = TREE_DEPTH as u8;
		let asset_id = 0;
		assert_err!(
			Anchor::create(
				Origin::signed(account::<AccountId>("", 1, SEED)),
				DEPOSIT_SIZE,
				max_edges,
				depth,
				asset_id
			),
			BadOrigin,
		);
	});
}

#[test]
fn should_be_able_to_deposit() {
	new_test_ext().execute_with(|| {
		setup_environment(Curve::Bn254);

		let max_edges = M as _;
		let depth = TREE_DEPTH as _;
		let asset_id = 0;
		assert_ok!(Anchor::create(Origin::root(), DEPOSIT_SIZE, max_edges, depth, asset_id));

		let tree_id = MerkleTree::next_tree_id() - 1;
		let account_id = account::<AccountId>("", 1, SEED);
		let leaf = Element::from_bytes(&[1u8; 32]);
		// check the balance before the deposit.
		let balance_before = Balances::free_balance(account_id.clone());
		println!("Balance before: {}", balance_before);
		// and we do the deposit
		assert_ok!(Anchor::deposit(Origin::signed(account_id.clone()), tree_id, leaf));
		// now we check the balance after the deposit.
		let balance_after = Balances::free_balance(account_id.clone());
		// the balance should be less now with `deposit_size`
		assert_eq!(balance_after, balance_before - DEPOSIT_SIZE);
		// now we need also to check if the state got updated.
		let tree = MerkleTree::trees(tree_id);
		assert_eq!(tree.leaf_count, 1);
		crate::mock::assert_last_event::<Test>(
			crate::Event::<Test>::Deposit {
				depositor: account_id,
				tree_id,
				leaf,
				amount: DEPOSIT_SIZE,
			}
			.into(),
		);
	});
}

#[test]
fn should_fail_to_deposit_if_anchor_not_found() {
	new_test_ext().execute_with(|| {
		setup_environment(Curve::Bn254);
		assert_err!(
			Anchor::deposit(
				Origin::signed(account::<AccountId>("", 1, SEED)),
				2,
				Element::from_bytes(&[1u8; 32])
			),
			crate::Error::<Test, _>::NoAnchorFound,
		);
	});
}

fn create_anchor(asset_id: u32) -> u32 {
	let max_edges = 2;
	let depth = TREE_DEPTH as u8;
	assert_ok!(Anchor::create(Origin::root(), DEPOSIT_SIZE, max_edges, depth, asset_id));
	MerkleTree::next_tree_id() - 1
}

#[test]
fn anchor_works() {
	new_test_ext().execute_with(|| {
		let curve = Curve::Bn254;
		let pk_bytes = setup_environment(curve);

		// inputs
		let tree_id = create_anchor(0);
		let src_chain_id = 1;
		let sender_account_id = account::<AccountId>("", 1, SEED);
		let recipient_account_id = account::<AccountId>("", 2, SEED);
		let relayer_account_id = account::<AccountId>("", 0, SEED);
		let fee_value = 0;
		let refund_value = 0;

		let recipient_bytes = crate::truncate_and_pad(&recipient_account_id.encode()[..]);
		let relayer_bytes = crate::truncate_and_pad(&relayer_account_id.encode()[..]);

		let (proof_bytes, roots_element, nullifier_hash_element, leaf_element) = setup_zk_circuit(
			curve,
			recipient_bytes,
			relayer_bytes,
			pk_bytes,
			src_chain_id,
			fee_value,
			refund_value,
		);

		assert_ok!(Anchor::deposit(
			Origin::signed(sender_account_id.clone()),
			tree_id,
			leaf_element.clone(),
		));

		let tree_root = MerkleTree::get_root(tree_id).unwrap();
		// sanity check.
		assert_eq!(roots_element[0], tree_root);

		let balance_before = Balances::free_balance(recipient_account_id.clone());
		// fire the call.
		assert_ok!(Anchor::withdraw(
			Origin::signed(sender_account_id),
			tree_id,
			proof_bytes,
			roots_element,
			nullifier_hash_element,
			recipient_account_id.clone(),
			relayer_account_id,
			fee_value.into(),
			refund_value.into(),
			leaf_element.clone(),
		));
		// now we check the recipient balance again.
		let balance_after = Balances::free_balance(recipient_account_id.clone());
		assert_eq!(balance_after, balance_before + DEPOSIT_SIZE);
		// perfect

		crate::mock::assert_last_event::<Test>(
			crate::Event::<Test>::Withdraw {
				who: recipient_account_id,
				amount: DEPOSIT_SIZE,
			}
			.into(),
		);
	});
}

#[test]
fn double_spending_should_fail() {
	new_test_ext().execute_with(|| {
		let curve = Curve::Bn254;
		let pk_bytes = setup_environment(curve);

		// inputs
		let tree_id = create_anchor(0);
		let src_chain_id = 1;
		let sender_account_id = account::<AccountId>("", 1, SEED);
		let recipient_account_id = account::<AccountId>("", 2, SEED);
		let relayer_account_id = account::<AccountId>("", 0, SEED);
		let fee_value = 0;
		let refund_value = 0;

		let recipient_bytes = crate::truncate_and_pad(&recipient_account_id.encode()[..]);
		let relayer_bytes = crate::truncate_and_pad(&relayer_account_id.encode()[..]);

		let (proof_bytes, roots_element, nullifier_hash_element, leaf_element) = setup_zk_circuit(
			curve,
			recipient_bytes,
			relayer_bytes,
			pk_bytes,
			src_chain_id,
			fee_value,
			refund_value,
		);

		assert_ok!(Anchor::deposit(
			Origin::signed(sender_account_id.clone()),
			tree_id,
			leaf_element.clone(),
		));

		let tree_root = MerkleTree::get_root(tree_id).unwrap();
		assert_eq!(roots_element[0], tree_root);
		// all ready, call withdraw.
		// but first check the balance before that.

		let balance_before = Balances::free_balance(recipient_account_id.clone());
		// fire the call.
		assert_ok!(Anchor::withdraw(
			Origin::signed(sender_account_id.clone()),
			tree_id,
			proof_bytes.clone(),
			roots_element.clone(),
			nullifier_hash_element,
			recipient_account_id.clone(),
			relayer_account_id.clone(),
			fee_value.into(),
			refund_value.into(),
			leaf_element.clone(),
		));
		// now we check the recipient balance again.
		let balance_after = Balances::free_balance(recipient_account_id.clone());
		assert_eq!(balance_after, balance_before + DEPOSIT_SIZE);
		// perfect

		// now double spending should fail.
		assert_err!(
			Anchor::withdraw(
				Origin::signed(sender_account_id),
				tree_id,
				proof_bytes,
				roots_element,
				nullifier_hash_element,
				recipient_account_id,
				relayer_account_id,
				fee_value.into(),
				refund_value.into(),
				leaf_element.clone(),
			),
			crate::Error::<Test, _>::AlreadyRevealedNullifier
		);
	});
}

#[test]
fn should_fail_when_invalid_merkle_roots() {
	new_test_ext().execute_with(|| {
		let curve = Curve::Bn254;
		let pk_bytes = setup_environment(curve);

		// inputs
		let tree_id = create_anchor(0);
		let src_chain_id = 1;
		let sender_account_id = account::<AccountId>("", 1, SEED);
		let recipient_account_id = account::<AccountId>("", 2, SEED);
		let relayer_account_id = account::<AccountId>("", 0, SEED);
		let fee_value = 0;
		let refund_value = 0;

		let recipient_bytes = crate::truncate_and_pad(&recipient_account_id.encode()[..]);
		let relayer_bytes = crate::truncate_and_pad(&relayer_account_id.encode()[..]);

		let (proof_bytes, mut roots_element, nullifier_hash_element, leaf_element) = setup_zk_circuit(
			curve,
			recipient_bytes,
			relayer_bytes,
			pk_bytes,
			src_chain_id,
			fee_value,
			refund_value,
		);

		assert_ok!(Anchor::deposit(
			Origin::signed(sender_account_id.clone()),
			tree_id,
			leaf_element.clone(),
		));

		let tree_root = MerkleTree::get_root(tree_id).unwrap();
		assert_eq!(roots_element[0], tree_root);

		// invalid root length
		roots_element.push(Element::from_bytes(
			&ark_bn254::Fr::default().into_repr().to_bytes_le()[..],
		));
		// all ready, call withdraw.

		// fire the call.
		assert_err!(
			Anchor::withdraw(
				Origin::signed(sender_account_id),
				tree_id,
				proof_bytes,
				roots_element,
				nullifier_hash_element,
				recipient_account_id,
				relayer_account_id,
				fee_value.into(),
				refund_value.into(),
				leaf_element.clone(),
			),
			pallet_linkable_tree::Error::<Test, _>::InvalidMerkleRoots,
		);
	});
}

#[test]
fn should_fail_with_when_any_byte_is_changed_in_proof() {
	new_test_ext().execute_with(|| {
		let curve = Curve::Bn254;
		let pk_bytes = setup_environment(curve);

		// inputs
		let tree_id = create_anchor(0);
		let src_chain_id = 1;
		let sender_account_id = account::<AccountId>("", 1, SEED);
		let recipient_account_id = account::<AccountId>("", 2, SEED);
		let relayer_account_id = account::<AccountId>("", 0, SEED);
		let fee_value = 0;
		let refund_value = 0;

		let recipient_bytes = crate::truncate_and_pad(&recipient_account_id.encode()[..]);
		let relayer_bytes = crate::truncate_and_pad(&relayer_account_id.encode()[..]);

		let (mut proof_bytes, roots_element, nullifier_hash_element, leaf_element) = setup_zk_circuit(
			curve,
			recipient_bytes,
			relayer_bytes,
			pk_bytes,
			src_chain_id,
			fee_value,
			refund_value,
		);

		assert_ok!(Anchor::deposit(
			Origin::signed(sender_account_id.clone()),
			tree_id,
			leaf_element.clone(),
		));

		let tree_root = MerkleTree::get_root(tree_id).unwrap();
		assert_eq!(roots_element[0], tree_root);

		// now double spending should fail.

		let a = proof_bytes[0];
		let b = proof_bytes[1];

		proof_bytes[0] = b;
		proof_bytes[1] = a;

		assert_err!(
			Anchor::withdraw(
				Origin::signed(sender_account_id),
				tree_id,
				proof_bytes,
				roots_element,
				nullifier_hash_element,
				recipient_account_id,
				relayer_account_id,
				fee_value.into(),
				refund_value.into(),
				leaf_element
			),
			crate::Error::<Test, _>::InvalidWithdrawProof
		);
	});
}

#[test]
fn should_fail_when_relayer_id_is_different_from_that_in_proof_generation() {
	new_test_ext().execute_with(|| {
		let curve = Curve::Bn254;
		let pk_bytes = setup_environment(curve);

		// inputs
		let tree_id = create_anchor(0);
		let src_chain_id = 1;
		let sender_account_id = account::<AccountId>("", 1, SEED);
		let recipient_account_id = account::<AccountId>("", 2, SEED);
		let relayer_account_id = account::<AccountId>("", 0, SEED);
		let fee_value = 0;
		let refund_value = 0;

		let recipient_bytes = crate::truncate_and_pad(&recipient_account_id.encode()[..]);
		let relayer_bytes = crate::truncate_and_pad(&relayer_account_id.encode()[..]);

		let (proof_bytes, roots_element, nullifier_hash_element, leaf_element) = setup_zk_circuit(
			curve,
			recipient_bytes,
			relayer_bytes,
			pk_bytes,
			src_chain_id,
			fee_value,
			refund_value,
		);

		assert_ok!(Anchor::deposit(
			Origin::signed(sender_account_id.clone()),
			tree_id,
			leaf_element.clone(),
		));

		let tree_root = MerkleTree::get_root(tree_id).unwrap();
		assert_eq!(roots_element[0], tree_root);

		assert_err!(
			Anchor::withdraw(
				Origin::signed(sender_account_id),
				tree_id,
				proof_bytes,
				roots_element,
				nullifier_hash_element,
				recipient_account_id.clone(),
				recipient_account_id,
				fee_value.into(),
				refund_value.into(),
				leaf_element,
			),
			crate::Error::<Test, _>::InvalidWithdrawProof
		);
	});
}

#[test]
fn should_fail_with_when_fee_submitted_is_changed() {
	new_test_ext().execute_with(|| {
		let curve = Curve::Bn254;
		let pk_bytes = setup_environment(curve);

		// inputs
		let tree_id = create_anchor(0);
		let src_chain_id = 1;
		let sender_account_id = account::<AccountId>("", 1, SEED);
		let recipient_account_id = account::<AccountId>("", 2, SEED);
		let relayer_account_id = account::<AccountId>("", 0, SEED);
		let fee_value = 0;
		let refund_value = 0;

		let recipient_bytes = crate::truncate_and_pad(&recipient_account_id.encode()[..]);
		let relayer_bytes = crate::truncate_and_pad(&relayer_account_id.encode()[..]);

		let (proof_bytes, roots_element, nullifier_hash_element, leaf_element) = setup_zk_circuit(
			curve,
			recipient_bytes,
			relayer_bytes,
			pk_bytes,
			src_chain_id,
			fee_value,
			refund_value,
		);

		assert_ok!(Anchor::deposit(
			Origin::signed(sender_account_id.clone()),
			tree_id,
			leaf_element.clone(),
		));

		let tree_root = MerkleTree::get_root(tree_id).unwrap();
		assert_eq!(roots_element[0], tree_root);

		// now double spending should fail.
		assert_err!(
			Anchor::withdraw(
				Origin::signed(sender_account_id),
				tree_id,
				proof_bytes,
				roots_element,
				nullifier_hash_element,
				recipient_account_id,
				relayer_account_id,
				100u128,
				refund_value.into(),
				leaf_element
			),
			crate::Error::<Test, _>::InvalidWithdrawProof
		);
	});
}

#[test]
fn should_fail_with_invalid_proof_when_account_ids_are_truncated_in_reverse() {
	new_test_ext().execute_with(|| {
		let curve = Curve::Bn254;
		let pk_bytes = setup_environment(curve);

		// inputs
		let tree_id = create_anchor(0);
		let src_chain_id = 1;
		let sender_account_id = account::<AccountId>("", 1, SEED);
		let recipient_account_id = account::<AccountId>("", 2, SEED);
		let relayer_account_id = account::<AccountId>("", 0, SEED);
		let fee_value = 0;
		let refund_value = 0;

		let recipient_bytes = truncate_and_pad_reverse(&recipient_account_id.encode()[..]);
		let relayer_bytes = truncate_and_pad_reverse(&relayer_account_id.encode()[..]);

		let (proof_bytes, roots_element, nullifier_hash_element, leaf_element) = setup_zk_circuit(
			curve,
			recipient_bytes,
			relayer_bytes,
			pk_bytes,
			src_chain_id,
			fee_value,
			refund_value,
		);

		assert_ok!(Anchor::deposit(
			Origin::signed(sender_account_id.clone()),
			tree_id,
			leaf_element.clone(),
		));

		let tree_root = MerkleTree::get_root(tree_id).unwrap();
		assert_eq!(roots_element[0], tree_root);

		// now double spending should fail.
		assert_err!(
			Anchor::withdraw(
				Origin::signed(sender_account_id),
				tree_id,
				proof_bytes,
				roots_element,
				nullifier_hash_element,
				recipient_account_id,
				relayer_account_id,
				fee_value.into(),
				refund_value.into(),
				leaf_element,
			),
			crate::Error::<Test, _>::InvalidWithdrawProof
		);
	});
}

#[test]
fn anchor_works_for_pool_tokens() {
	new_test_ext().execute_with(|| {
		let existential_balance: u32 = 1000;
		let first_token_id = AssetRegistry::register_asset(
			b"shib".to_vec().try_into().unwrap(),
			AssetType::Token,
			existential_balance.into(),
		)
		.unwrap();
		let second_token_id = AssetRegistry::register_asset(
			b"doge".to_vec().try_into().unwrap(),
			AssetType::Token,
			existential_balance.into(),
		)
		.unwrap();

		let pool_share_id = AssetRegistry::register_asset(
			b"meme".to_vec().try_into().unwrap(),
			AssetType::PoolShare(vec![second_token_id, first_token_id]),
			existential_balance.into(),
		)
		.unwrap();

		let curve = Curve::Bn254;
		let pk_bytes = setup_environment(curve);

		// inputs
		let tree_id = create_anchor(pool_share_id);
		let src_chain_id = 1;
		let sender_account_id = account::<AccountId>("", 1, SEED);
		let recipient_account_id = account::<AccountId>("", 2, SEED);
		let relayer_account_id = account::<AccountId>("", 0, SEED);
		let fee_value = 0;
		let refund_value = 0;
		let balance = 30_000u32;

		assert_ok!(Currencies::update_balance(
			Origin::root(),
			sender_account_id.clone(),
			first_token_id,
			balance.into()
		));

		assert_ok!(Currencies::update_balance(
			Origin::root(),
			sender_account_id.clone(),
			second_token_id,
			balance.into()
		));

		assert_ok!(TokenWrapper::set_wrapping_fee(Origin::root(), 0));

		assert_ok!(TokenWrapper::wrap(
			Origin::signed(sender_account_id.clone()),
			first_token_id,
			pool_share_id,
			10000 as u128,
			sender_account_id.clone()
		));

		assert_ok!(TokenWrapper::wrap(
			Origin::signed(sender_account_id.clone()),
			second_token_id,
			pool_share_id,
			10000 as u128,
			sender_account_id.clone()
		));

		assert_eq!(Tokens::total_issuance(pool_share_id), 20_000u32.into());

		let recipient_bytes = crate::truncate_and_pad(&recipient_account_id.encode()[..]);
		let relayer_bytes = crate::truncate_and_pad(&relayer_account_id.encode()[..]);

		let (proof_bytes, roots_element, nullifier_hash_element, leaf_element) = setup_zk_circuit(
			curve,
			recipient_bytes,
			relayer_bytes,
			pk_bytes,
			src_chain_id,
			fee_value,
			refund_value,
		);

		assert_ok!(Anchor::deposit(
			Origin::signed(sender_account_id.clone()),
			tree_id,
			leaf_element.clone(),
		));

		let tree_root = MerkleTree::get_root(tree_id).unwrap();
		// sanity check.
		assert_eq!(roots_element[0], tree_root);

		let balance_before = TokenWrapper::get_balance(pool_share_id, &recipient_account_id); // fire the call.
		assert_ok!(Anchor::withdraw(
			Origin::signed(sender_account_id),
			tree_id,
			proof_bytes,
			roots_element,
			nullifier_hash_element,
			recipient_account_id.clone(),
			relayer_account_id,
			fee_value.into(),
			refund_value.into(),
			leaf_element.clone(),
		));
		// now we check the recipient balance again.
		let balance_after = TokenWrapper::get_balance(pool_share_id, &recipient_account_id);
		assert_eq!(balance_after, balance_before + DEPOSIT_SIZE);

		assert_ok!(TokenWrapper::unwrap(
			Origin::signed(recipient_account_id.clone()),
			pool_share_id,
			second_token_id,
			10000 as u128,
			recipient_account_id.clone()
		));

		assert_eq!(Tokens::total_issuance(pool_share_id), 10000u32.into());

		assert_eq!(TokenWrapper::get_balance(second_token_id, &recipient_account_id), 10000);
	});
}

#[test]
fn should_run_post_deposit_hook_sucessfully() {
	new_test_ext().execute_with(|| {
		setup_environment(Curve::Bn254);

		let max_edges = M as _;
		let depth = TREE_DEPTH as _;
		let asset_id = 0;
		assert_ok!(Anchor::create(Origin::root(), DEPOSIT_SIZE, max_edges, depth, asset_id));

		let tree_id = MerkleTree::next_tree_id() - 1;
		let account_id = account::<AccountId>("", 1, SEED);
		let leaf = Element::from_bytes(&[1u8; 32]);
		// check the balance before the deposit.
		let balance_before = Balances::free_balance(account_id.clone());
		println!("Balance before: {}", balance_before);
		// and we do the deposit
		assert_ok!(Anchor::deposit_and_update_linked_anchors(
			Origin::signed(account_id.clone()),
			tree_id,
			leaf
		));
		// now we check the balance after the deposit.
		let balance_after = Balances::free_balance(account_id.clone());
		// the balance should be less now with `deposit_size`
		assert_eq!(balance_after, balance_before - DEPOSIT_SIZE);
		// now we need also to check if the state got updated.
		let tree = MerkleTree::trees(tree_id);
		crate::mock::assert_last_event::<Test>(
			crate::Event::<Test>::PostDeposit {
				depositor: account_id,
				tree_id,
				leaf,
			}
			.into(),
		);
	});
}
