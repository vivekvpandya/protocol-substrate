#![allow(clippy::zero_prefixed_literal)]

use super::*;
use crate as pallet_mixer;
use codec::Decode;
use frame_support::traits::GenesisBuild;
use sp_core::H256;
use webb_primitives::verifying::ArkworksVerifierBn254;

use frame_support::{parameter_types, traits::Nothing};
use frame_system as system;
use orml_currencies::BasicCurrencyAdapter;
use serde::{Deserialize, Serialize};
use sp_runtime::{
	testing::Header,
	traits::{BlakeTwo256, IdentityLookup},
};
pub use webb_primitives::hasher::{HasherModule, InstanceHasher};
use webb_primitives::{hashing::ethereum::Keccak256HasherBn254, types::ElementTrait, AccountId};

use frame_benchmarking::account;

type UncheckedExtrinsic = frame_system::mocking::MockUncheckedExtrinsic<Test>;
type Block = frame_system::mocking::MockBlock<Test>;
type BlockNumber = u64;

// Configure a mock runtime to test the pallet.
frame_support::construct_runtime!(
	pub enum Test where
		Block = Block,
		NodeBlock = Block,
		UncheckedExtrinsic = UncheckedExtrinsic,
	{
		System: frame_system::{Pallet, Call, Config, Storage, Event<T>},
		Balances: pallet_balances::<Instance1>::{Pallet, Call, Storage, Event<T>},
		Balances2: pallet_balances::<Instance2>::{Pallet, Call, Storage, Event<T>},
		Assets: pallet_assets::{Pallet, Call, Storage, Event<T>},
		HasherPallet: pallet_hasher::{Pallet, Call, Storage, Event<T>},
		VerifierPallet: pallet_verifier::{Pallet, Call, Storage, Event<T>},
		MerkleTree: pallet_mt::<Instance1>::{Pallet, Call, Storage, Event<T>},
		Mixer: pallet_mixer::<Instance1>::{Pallet, Call, Storage, Event<T>},
		MerkleTree2: pallet_mt::<Instance2>::{Pallet, Call, Storage, Event<T>},
		Mixer2: pallet_mixer::<Instance2>::{Pallet, Call, Storage, Event<T>},
		AssetRegistry: pallet_asset_registry::{Pallet, Call, Storage, Event<T>},
		Currencies: orml_currencies::{Pallet, Call, Event<T>},
		Tokens: orml_tokens::{Pallet, Storage, Call, Event<T>},
	}
);

parameter_types! {
	pub const BlockHashCount: u64 = 250;
	pub const SS58Prefix: u8 = 42;
}

impl system::Config for Test {
	type AccountData = pallet_balances::AccountData<u128>;
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

impl pallet_balances::Config<Instance1> for Test {
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

impl pallet_balances::Config<Instance2> for Test {
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
	pub const AssetDeposit : Balance = 0;
	pub const AssetAccountDeposit : Balance = 1;
	pub const MetadataDepositBaseForAssets: Balance = 1;
	pub const MetadataDepositPerByteForAssets: Balance = 1;
	pub const ApprovalDeposit: Balance = 1;
	pub const StringLimitForAssets: u32 = 32;
}

impl pallet_assets::Config for Test {
	type Event = Event;
	type Balance = Balance;
	type AssetId = webb_primitives::AssetId;
	type Currency = Balances2;
	type WeightInfo = ();
	type Extra = ();
	type ForceOrigin = frame_system::EnsureRoot<AccountId>;
	type AssetDeposit = AssetDeposit;
	type AssetAccountDeposit = AssetAccountDeposit;
	type MetadataDepositBase = MetadataDepositBaseForAssets;
	type MetadataDepositPerByte = MetadataDepositPerByteForAssets;
	type ApprovalDeposit = ApprovalDeposit;
	type StringLimit = StringLimitForAssets;
	type Freezer = ();
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
	pub const NewDefaultZeroElement: Element = Element([0u8; 32]);
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
	Deserialize,
	Serialize,
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

impl pallet_mt::Config<pallet_mt::Instance1> for Test {
	type Currency = Balances;
	type DataDepositBase = LeafDepositBase;
	type DataDepositPerByte = LeafDepositPerByte;
	type DefaultZeroElement = NewDefaultZeroElement;
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

impl pallet_mt::Config<pallet_mt::Instance2> for Test {
	type Currency = Balances2;
	type DataDepositBase = LeafDepositBase;
	type DataDepositPerByte = LeafDepositPerByte;
	type DefaultZeroElement = NewDefaultZeroElement;
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

impl pallet_verifier::Config for Test {
	type Event = Event;
	type ForceOrigin = frame_system::EnsureRoot<AccountId>;
	type Verifier = ArkworksVerifierBn254;
	type WeightInfo = ();
}

parameter_types! {
	pub const NativeAssetId: AssetId = 0;
	pub const RegistryStringLimit: u32 = 10;
}

/// Type for storing the id of an asset.
pub type AssetId = u32;
/// Signed version of Balance
pub type Amount = i128;
/// balance type
pub type Balance = u128;

impl pallet_asset_registry::Config for Test {
	type AssetId = webb_primitives::AssetId;
	type AssetNativeLocation = ();
	type Balance = Balance;
	type Event = Event;
	type NativeAssetId = NativeAssetId;
	type RegistryOrigin = frame_system::EnsureRoot<AccountId>;
	type StringLimit = RegistryStringLimit;
	type WeightInfo = ();
}

/// Tokens Configurations
impl orml_tokens::Config for Test {
	type Amount = Amount;
	type Balance = Balance;
	type CurrencyId = webb_primitives::AssetId;
	type DustRemovalWhitelist = Nothing;
	type Event = Event;
	type ExistentialDeposits = AssetRegistry;
	type MaxLocks = ();
	type OnDust = ();
	type WeightInfo = ();
}

impl orml_currencies::Config for Test {
	type Event = Event;
	type GetNativeCurrencyId = NativeAssetId;
	type MultiCurrency = Tokens;
	type NativeCurrency = BasicCurrencyAdapter<Test, Balances, Amount, BlockNumber>;
	type WeightInfo = ();
}

parameter_types! {
	pub const MixerPalletId: PalletId = PalletId(*b"py/mixer");
	pub const NativeCurrencyId: AssetId = 0;
}

impl Config<pallet_mixer::Instance1> for Test {
	type CurrencyId = webb_primitives::AssetId;
	type Balance = Balance;
	type Currency = Combiner<
		webb_primitives::AssetId,
		AccountId,
		Balance,
		// UsePalletAssets,
		UseOrmlCurrency,
		Currencies,
		Assets,
	>;
	type Event = Event;
	type NativeCurrencyId = NativeCurrencyId;
	type PalletId = MixerPalletId;
	type Tree = MerkleTree;
	type Verifier = VerifierPallet;
	type ArbitraryHasher = Keccak256HasherBn254;
	type WeightInfo = ();
}

parameter_types! {
	pub const MixerPalletId2: PalletId = PalletId(*b"py/mixe2");
	pub const NativeCurrencyId2: AssetId = 0;
}

impl Config<pallet_mixer::Instance2> for Test {
	type CurrencyId = webb_primitives::AssetId;
	type Balance = Balance;
	type Currency = Combiner<
		webb_primitives::AssetId,
		AccountId,
		Balance,
		UsePalletAssets,
		// UseOrmlCurrency,
		Currencies,
		Assets,
	>;
	type Event = Event;
	type NativeCurrencyId = NativeCurrencyId2;
	type PalletId = MixerPalletId2;
	type Tree = MerkleTree2;
	type Verifier = VerifierPallet;
	type ArbitraryHasher = Keccak256HasherBn254;
	type WeightInfo = ();
}

// Build genesis storage according to the mock runtime.
pub fn new_test_ext() -> sp_io::TestExternalities {
	use sp_runtime::traits::Zero;
	let mut storage = system::GenesisConfig::default().build_storage::<Test>().unwrap();
	pallet_assets::GenesisConfig::<Test> {
		assets: vec![
			(0, account::<AccountId>("", 1, 0), true, 1),
			(1, account::<AccountId>("", 1, 0), true, 1),
		], // (id, owner, is_sufficient, min_balance)
		metadata: vec![
			(0, "NATIVE_TOKEN".into(), "WEBB".into(), 12),
			(1, "ETHER".into(), "ETH".into(), 12),
		], // (id, name, symbol, decimals)
		accounts: vec![
			(0, account::<AccountId>("", 1, 0), 100_000_000),
			(0, account::<AccountId>("", 2, 0), 100_000_000),
			(0, account::<AccountId>("", 3, 0), 100_000_000),
			(0, account::<AccountId>("", 4, 0), 100_000_000),
			(0, account::<AccountId>("", 5, 0), 100_000_000),
			(0, account::<AccountId>("", 6, 0), 100_000_000),
			(1, account::<AccountId>("", 1, 0), 0),
		], // (id, account_id, balance)
	}
	.assimilate_storage(&mut storage)
	.unwrap();
	pallet_asset_registry::GenesisConfig::<Test> {
		asset_names: vec![],
		native_asset_name: b"UNIT".to_vec(),
		native_existential_deposit: Zero::zero(),
	}
	.assimilate_storage(&mut storage)
	.unwrap();
	storage.into()
}
