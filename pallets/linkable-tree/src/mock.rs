#![allow(clippy::zero_prefixed_literal)]

use super::*;
use crate as pallet_linkable_tree;
use codec::{Decode, Encode};
use sp_core::H256;

use frame_support::parameter_types;
use frame_system as system;
use serde::{Deserialize, Serialize};
use sp_runtime::{
	testing::Header,
	traits::{BlakeTwo256, IdentityLookup},
};
pub use webb_primitives::{
	hasher::{HasherModule, InstanceHasher},
	types::ElementTrait,
	AccountId,
};

type UncheckedExtrinsic = frame_system::mocking::MockUncheckedExtrinsic<Test>;
type Block = frame_system::mocking::MockBlock<Test>;

pub type Balance = u128;
pub type ChainId = u64;

pub type BlockNumber = u64;
/// Type for storing the id of an asset.
pub type AssetId = u32;
/// Signed version of Balance
pub type Amount = i128;
pub type CurrencyId = u32;

// Configure a mock runtime to test the pallet.
frame_support::construct_runtime!(
	pub enum Test where
		Block = Block,
		NodeBlock = Block,
		UncheckedExtrinsic = UncheckedExtrinsic,
	{
		System: frame_system::{Pallet, Call, Config, Storage, Event<T>},
		Balances: pallet_balances::{Pallet, Call, Storage, Event<T>},
		HasherPallet: pallet_hasher::{Pallet, Call, Storage, Event<T>},
		MerkleTree: pallet_mt::{Pallet, Call, Storage, Event<T>},
		LinkableTree: pallet_linkable_tree::{Pallet, Call, Storage, Event<T>},
	}
);

parameter_types! {
	pub const BlockHashCount: u64 = 250;
	pub const SS58Prefix: u8 = 42;
}

impl system::Config for Test {
	type AccountData = pallet_balances::AccountData<Balance>;
	type AccountId = AccountId;
	type BaseCallFilter = frame_support::traits::Everything;
	type BlockHashCount = BlockHashCount;
	type BlockLength = ();
	type BlockNumber = BlockNumber;
	type BlockWeights = ();
	type Call = Call;
	type DbWeight = ();
	type Event = Event;
	type Hash = H256;
	type Hashing = BlakeTwo256;
	type Header = Header;
	type Index = u64;
	type Lookup = IdentityLookup<Self::AccountId>;
	type MaxConsumers = frame_support::traits::ConstU32<16>;
	type OnKilledAccount = ();
	type OnNewAccount = ();
	type OnSetCode = ();
	type Origin = Origin;
	type PalletInfo = PalletInfo;
	type SS58Prefix = SS58Prefix;
	type SystemWeightInfo = ();
	type Version = ();
}

parameter_types! {
	pub const ExistentialDeposit: u64 = 1;
}

impl pallet_balances::Config for Test {
	type AccountStore = System;
	type Balance = Balance;
	type DustRemoval = ();
	type Event = Event;
	type ExistentialDeposit = ExistentialDeposit;
	type MaxLocks = ();
	type MaxReserves = ();
	type ReserveIdentifier = [u8; 8];
	type WeightInfo = ();
}

parameter_types! {
	pub const ParameterDeposit: u64 = 1;
	pub const StringLimit: u32 = 50;
	pub const MetadataDepositBase: u64 = 1;
	pub const MetadataDepositPerByte: u64 = 1;
}

impl pallet_hasher::Config for Test {
	type Event = Event;
	type ForceOrigin = frame_system::EnsureRoot<AccountId>;
	type Hasher = webb_primitives::hashing::ArkworksPoseidonHasherBn254;
	type WeightInfo = ();
}

parameter_types! {
	pub const TreeDeposit: u64 = 1;
	pub const LeafDepositBase: u64 = 1;
	pub const LeafDepositPerByte: u64 = 1;
	pub const Two: u64 = 2;
	pub const MaxTreeDepth: u8 = 30;
	pub const RootHistorySize: u32 = 1096;
	// 21663839004416932945382355908790599225266501822907911457504978515578255421292
	pub const DefaultZeroElement: Element = Element([
		108, 175, 153, 072, 237, 133, 150, 036,
		226, 065, 231, 118, 015, 052, 027, 130,
		180, 093, 161, 235, 182, 053, 058, 052,
		243, 171, 172, 211, 096, 076, 229, 047,
	]);
	pub const MockZeroElement: Element = Element([0; 32]);
}

#[derive(
	Debug,
	Encode,
	Decode,
	Default,
	Copy,
	Clone,
	PartialEq,
	Eq,
	scale_info::TypeInfo,
	Serialize,
	Deserialize,
)]
pub struct Element([u8; 32]);

impl ElementTrait for Element {
	fn to_bytes(&self) -> &[u8] {
		&self.0
	}

	fn from_bytes(input: &[u8]) -> Self {
		let mut buf = [0u8; 32];
		buf.copy_from_slice(input);
		Self(buf)
	}
}

impl pallet_mt::Config for Test {
	type Currency = Balances;
	type DataDepositBase = LeafDepositBase;
	type DataDepositPerByte = LeafDepositPerByte;
	type DefaultZeroElement = MockZeroElement;
	type Element = Element;
	type Event = Event;
	type ForceOrigin = frame_system::EnsureRoot<AccountId>;
	type Hasher = HasherPallet;
	type LeafIndex = u32;
	type MaxTreeDepth = MaxTreeDepth;
	type RootHistorySize = RootHistorySize;
	type RootIndex = u32;
	type StringLimit = StringLimit;
	type TreeDeposit = TreeDeposit;
	type TreeId = u32;
	type Two = Two;
	type WeightInfo = ();
}

parameter_types! {
	pub const NativeCurrencyId: AssetId = 0;
	pub const RegistryStringLimit: u32 = 10;
}

parameter_types! {
	pub const HistoryLength: u32 = 30;
	// Substrate standalone chain ID type
	pub const ChainType: [u8; 2] = [2, 0];
	pub const CurrentChainId: ChainId = 0;
}

impl pallet_linkable_tree::Config for Test {
	type ChainId = ChainId;
	type ChainType = ChainType;
	type ChainIdentifier = CurrentChainId;
	type Event = Event;
	type HistoryLength = HistoryLength;
	type Tree = MerkleTree;
	type WeightInfo = ();
}

// Build genesis storage according to the mock runtime.
pub fn new_test_ext() -> sp_io::TestExternalities {
	system::GenesisConfig::default().build_storage::<Test>().unwrap().into()
}
