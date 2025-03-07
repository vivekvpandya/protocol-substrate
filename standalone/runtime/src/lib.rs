#![allow(clippy::from_over_into, non_snake_case)]
#![cfg_attr(not(feature = "std"), no_std)]
#![recursion_limit = "256"]

// Make the WASM binary available.
#[cfg(feature = "std")]
include!(concat!(env!("OUT_DIR"), "/wasm_binary.rs"));

pub mod constants;
use common::*;
use constants::{currency::*, time::*};
pub mod impls;
mod voter_bags;
mod weights;
use frame_support::traits::EnsureOneOf;
use impls::Author;
use sp_api::impl_runtime_apis;
use sp_core::{
	crypto::KeyTypeId,
	u32_trait::{_1, _2, _3, _4, _5},
	OpaqueMetadata,
};
use static_assertions::const_assert;

use frame_support::{traits::EqualPrivilegeOnly, weights::constants::RocksDbWeight};
use pallet_grandpa::{
	fg_primitives, AuthorityId as GrandpaId, AuthorityList as GrandpaAuthorityList,
};
use pallet_im_online::sr25519::AuthorityId as ImOnlineId;
use pallet_session::historical as pallet_session_historical;
pub use pallet_transaction_payment::{CurrencyAdapter, Multiplier, TargetedFeeAdjustment};
use pallet_transaction_payment::{FeeDetails, RuntimeDispatchInfo};
use sp_authority_discovery::AuthorityId as AuthorityDiscoveryId;
use sp_runtime::{
	create_runtime_str,
	curve::PiecewiseLinear,
	generic,
	generic::Era,
	impl_opaque_keys,
	traits::{
		self, BlakeTwo256, Block as BlockT, NumberFor, OpaqueKeys, SaturatedConversion,
		StaticLookup,
	},
	transaction_validity::{TransactionPriority, TransactionSource, TransactionValidity},
	ApplyExtrinsicResult, FixedPointNumber, Perbill, Percent, Permill, Perquintill,
};
use sp_std::prelude::*;

#[cfg(feature = "std")]
use sp_version::NativeVersion;
use sp_version::RuntimeVersion;

#[cfg(any(feature = "std", test))]
pub use frame_system::Call as SystemCall;
#[cfg(any(feature = "std", test))]
pub use pallet_balances::Call as BalancesCall;
#[cfg(any(feature = "std", test))]
pub use pallet_staking::StakerStatus;
#[cfg(any(feature = "std", test))]
pub use sp_runtime::BuildStorage;

use pallet_election_provider_multi_phase::NoFallback;

#[cfg(feature = "std")]
use serde::{Deserialize, Serialize};

use codec::{Decode, Encode, MaxEncodedLen};
use frame_support::{
	construct_runtime,
	pallet_prelude::ConstU32,
	parameter_types,
	traits::{
		ConstU128, Currency, Everything, Imbalance, InstanceFilter, KeyOwnerProofSystem,
		LockIdentifier, OnUnbalanced, U128CurrencyToVote,
	},
	weights::{
		constants::{BlockExecutionWeight, ExtrinsicBaseWeight},
		DispatchClass, IdentityFee, Weight,
	},
	PalletId, RuntimeDebug,
};
use frame_system::{
	limits::{BlockLength, BlockWeights},
	EnsureRoot,
};

use frame_support::traits::Nothing;
use orml_currencies::BasicCurrencyAdapter;
use webb_primitives::{
	field_ops::arkworks::ArkworksIntoFieldBn254,
	hashing::{ethereum::Keccak256HasherBn254, ArkworksPoseidonHasherBn254},
	types::ElementTrait,
	verifying::ArkworksVerifierBn254,
	Amount, ChainId,
};

impl_opaque_keys! {
	pub struct SessionKeys {
		pub grandpa: Grandpa,
		pub babe: Babe,
		pub im_online: ImOnline,
		pub authority_discovery: AuthorityDiscovery,
	}
}

/// Wasm binary unwrapped. If built with `SKIP_WASM_BUILD`, the function panics.
#[cfg(feature = "std")]
pub fn wasm_binary_unwrap() -> &'static [u8] {
	WASM_BINARY.expect(
		"Development wasm binary is not available. This means the client is built with \
		 `SKIP_WASM_BUILD` flag and it is only usable for production chains. Please rebuild with \
		 the flag disabled.",
	)
}

#[sp_version::runtime_version]
pub const VERSION: RuntimeVersion = RuntimeVersion {
	spec_name: create_runtime_str!("webb"),
	impl_name: create_runtime_str!("webb"),
	authoring_version: 1,
	spec_version: 3,
	impl_version: 0,
	apis: RUNTIME_API_VERSIONS,
	transaction_version: 1,
	state_version: 1,
};

/// The BABE epoch configuration at genesis.
pub const BABE_GENESIS_EPOCH_CONFIG: sp_consensus_babe::BabeEpochConfiguration =
	sp_consensus_babe::BabeEpochConfiguration {
		c: PRIMARY_PROBABILITY,
		allowed_slots: sp_consensus_babe::AllowedSlots::PrimaryAndSecondaryPlainSlots,
	};

/// The version information used to identify this runtime when compiled
/// natively.
#[cfg(feature = "std")]
pub fn native_version() -> NativeVersion {
	NativeVersion { runtime_version: VERSION, can_author_with: Default::default() }
}

type NegativeImbalance = <Balances as Currency<AccountId>>::NegativeImbalance;

pub struct DealWithFees;
impl OnUnbalanced<NegativeImbalance> for DealWithFees {
	fn on_unbalanceds<B>(mut fees_then_tips: impl Iterator<Item = NegativeImbalance>) {
		if let Some(fees) = fees_then_tips.next() {
			// for fees, 80% to treasury, 20% to author
			let mut split = fees.ration(80, 20);
			if let Some(tips) = fees_then_tips.next() {
				// for tips, if any, 80% to treasury, 20% to author (though this can be
				// anything)
				tips.ration_merge_into(80, 20, &mut split);
			}
			Treasury::on_unbalanced(split.0);
			Author::on_unbalanced(split.1);
		}
	}
}

parameter_types! {
	pub const BlockHashCount: BlockNumber = 2400;
	pub const Version: RuntimeVersion = VERSION;
	pub RuntimeBlockLength: BlockLength =
		BlockLength::max_with_normal_ratio(5 * 1024 * 1024, NORMAL_DISPATCH_RATIO);
	pub RuntimeBlockWeights: BlockWeights = BlockWeights::builder()
		.base_block(BlockExecutionWeight::get())
		.for_class(DispatchClass::all(), |weights| {
			weights.base_extrinsic = ExtrinsicBaseWeight::get();
		})
		.for_class(DispatchClass::Normal, |weights| {
			weights.max_total = Some(NORMAL_DISPATCH_RATIO * MAXIMUM_BLOCK_WEIGHT);
		})
		.for_class(DispatchClass::Operational, |weights| {
			weights.max_total = Some(MAXIMUM_BLOCK_WEIGHT);
			// Operational transactions have some extra reserved space, so that they
			// are included even if block reached `MAXIMUM_BLOCK_WEIGHT`.
			weights.reserved = Some(
				MAXIMUM_BLOCK_WEIGHT - NORMAL_DISPATCH_RATIO * MAXIMUM_BLOCK_WEIGHT
			);
		})
		.avg_block_initialization(AVERAGE_ON_INITIALIZE_RATIO)
		.build_or_panic();
	pub const SS58Prefix: u16 = 42;
}

impl frame_system::Config for Runtime {
	type AccountData = pallet_balances::AccountData<Balance>;
	type AccountId = AccountId;
	type BaseCallFilter = Everything;
	type BlockHashCount = BlockHashCount;
	type BlockLength = RuntimeBlockLength;
	type BlockNumber = BlockNumber;
	type BlockWeights = RuntimeBlockWeights;
	type Call = Call;
	type DbWeight = RocksDbWeight;
	type Event = Event;
	type Hash = Hash;
	type Hashing = BlakeTwo256;
	type Header = generic::Header<BlockNumber, BlakeTwo256>;
	type Index = Index;
	type Lookup = Indices;
	type MaxConsumers = frame_support::traits::ConstU32<16>;
	type OnKilledAccount = ();
	type OnNewAccount = ();
	type OnSetCode = ();
	type Origin = Origin;
	type PalletInfo = PalletInfo;
	type SS58Prefix = SS58Prefix;
	type SystemWeightInfo = frame_system::weights::SubstrateWeight<Runtime>;
	type Version = Version;
}

parameter_types! {
	pub const MinimumPeriod: u64 = SLOT_DURATION / 2;
}

impl pallet_timestamp::Config for Runtime {
	type MinimumPeriod = MinimumPeriod;
	type Moment = Moment;
	type OnTimestampSet = Babe;
	type WeightInfo = pallet_timestamp::weights::SubstrateWeight<Runtime>;
}

parameter_types! {
	pub const UncleGenerations: u32 = 0;
}

impl pallet_authorship::Config for Runtime {
	type EventHandler = (Staking, ImOnline);
	type FilterUncle = ();
	type FindAuthor = pallet_session::FindAccountFromAuthorIndex<Self, Babe>;
	type UncleGenerations = UncleGenerations;
}

parameter_types! {
	pub const ExistentialDeposit: Balance = EXISTENTIAL_DEPOSIT;
	pub const MaxLocks: u32 = 50;
	pub const MaxReserves: u32 = 50;
}

impl pallet_balances::Config for Runtime {
	type AccountStore = System;
	/// The type for recording an account's balance.
	type Balance = Balance;
	type DustRemoval = ();
	/// The ubiquitous event type.
	type Event = Event;
	type ExistentialDeposit = ExistentialDeposit;
	type MaxLocks = MaxLocks;
	type MaxReserves = MaxReserves;
	type ReserveIdentifier = [u8; 8];
	type WeightInfo = weights::pallet_balances::WeightInfo<Runtime>;
}

parameter_types! {
	pub const TransactionByteFee: Balance = 10 * MILLICENTS;
	pub const OperationalFeeMultiplier: u8 = 5;
	pub const TargetBlockFullness: Perquintill = Perquintill::from_percent(25);
	pub AdjustmentVariable: Multiplier = Multiplier::saturating_from_rational(1, 100_000);
	pub MinimumMultiplier: Multiplier = Multiplier::saturating_from_rational(1, 1_000_000_000u128);
}

impl pallet_transaction_payment::Config for Runtime {
	type FeeMultiplierUpdate =
		TargetedFeeAdjustment<Self, TargetBlockFullness, AdjustmentVariable, MinimumMultiplier>;
	type OnChargeTransaction = CurrencyAdapter<Balances, DealWithFees>;
	type OperationalFeeMultiplier = OperationalFeeMultiplier;
	type TransactionByteFee = TransactionByteFee;
	type WeightToFee = IdentityFee<Balance>;
}

parameter_types! {
	// NOTE: Currently it is not possible to change the epoch duration after the chain has started.
	//       Attempting to do so will brick block production.
	pub const EpochDuration: u64 = EPOCH_DURATION_IN_SLOTS;
	pub const ExpectedBlockTime: Moment = MILLISECS_PER_BLOCK;
	pub const ReportLongevity: u64 =
		BondingDuration::get() as u64 * SessionsPerEra::get() as u64 * EpochDuration::get();
}

parameter_types! {
	pub MaximumSchedulerWeight: Weight = Perbill::from_percent(80) *
		RuntimeBlockWeights::get().max_block;
	// Retry a scheduled item every 10 blocks (1 minute) until the preimage exists.
	pub const NoPreimagePostponement: Option<u32> = Some(10);
}

impl pallet_scheduler::Config for Runtime {
	type Call = Call;
	type Event = Event;
	type MaxScheduledPerBlock = ConstU32<50>;
	type MaximumWeight = MaximumSchedulerWeight;
	type NoPreimagePostponement = NoPreimagePostponement;
	type Origin = Origin;
	type OriginPrivilegeCmp = EqualPrivilegeOnly;
	type PalletsOrigin = OriginCaller;
	type PreimageProvider = Preimage;
	type ScheduleOrigin = EnsureRoot<AccountId>;
	type WeightInfo = pallet_scheduler::weights::SubstrateWeight<Runtime>;
}

parameter_types! {
	pub const PreimageMaxSize: u32 = 4096 * 1024;
	pub const PreimageBaseDeposit: Balance = 1 * DOLLARS;
}

impl pallet_preimage::Config for Runtime {
	type BaseDeposit = PreimageBaseDeposit;
	type ByteDeposit = PreimageByteDeposit;
	type Currency = Balances;
	type Event = Event;
	type ManagerOrigin = EnsureRoot<AccountId>;
	type MaxSize = PreimageMaxSize;
	type WeightInfo = pallet_preimage::weights::SubstrateWeight<Runtime>;
}

impl pallet_babe::Config for Runtime {
	type DisabledValidators = Session;
	type EpochChangeTrigger = pallet_babe::ExternalTrigger;
	type EpochDuration = EpochDuration;
	type ExpectedBlockTime = ExpectedBlockTime;
	type HandleEquivocation =
		pallet_babe::EquivocationHandler<Self::KeyOwnerIdentification, Offences, ReportLongevity>;
	type KeyOwnerIdentification = <Self::KeyOwnerProofSystem as KeyOwnerProofSystem<(
		KeyTypeId,
		pallet_babe::AuthorityId,
	)>>::IdentificationTuple;
	type KeyOwnerProof = <Self::KeyOwnerProofSystem as KeyOwnerProofSystem<(
		KeyTypeId,
		pallet_babe::AuthorityId,
	)>>::Proof;
	type KeyOwnerProofSystem = Historical;
	type MaxAuthorities = MaxAuthorities;
	type WeightInfo = ();
}

parameter_types! {
	pub const IndexDeposit: Balance = 1 * DOLLARS;
}

impl pallet_indices::Config for Runtime {
	type AccountIndex = AccountIndex;
	type Currency = Balances;
	type Deposit = IndexDeposit;
	type Event = Event;
	type WeightInfo = pallet_indices::weights::SubstrateWeight<Runtime>;
}

impl pallet_session::Config for Runtime {
	type Event = Event;
	type Keys = SessionKeys;
	type NextSessionRotation = Babe;
	type SessionHandler = <SessionKeys as OpaqueKeys>::KeyTypeIdProviders;
	type SessionManager = pallet_session::historical::NoteHistoricalRoot<Self, Staking>;
	type ShouldEndSession = Babe;
	type ValidatorId = <Self as frame_system::Config>::AccountId;
	type ValidatorIdOf = pallet_staking::StashOf<Self>;
	type WeightInfo = pallet_session::weights::SubstrateWeight<Runtime>;
}

impl pallet_session::historical::Config for Runtime {
	type FullIdentification = pallet_staking::Exposure<AccountId, Balance>;
	type FullIdentificationOf = pallet_staking::ExposureOf<Runtime>;
}

pallet_staking_reward_curve::build! {
	const REWARD_CURVE: PiecewiseLinear<'static> = curve!(
		min_inflation: 0_040_000,
		max_inflation: 0_050_000,
		// 60% of total issuance at a yearly inflation rate of 5%
		ideal_stake: 0_600_000,
		falloff: 0_050_000,
		max_piece_count: 40,
		test_precision: 0_005_000,
	);
}

parameter_types! {
	pub const OffendingValidatorsThreshold: Perbill = Perbill::from_percent(17);
	pub const SessionsPerEra: sp_staking::SessionIndex = 6;
	pub const BondingDuration: sp_staking::EraIndex = 24 * 28;
	pub const SlashDeferDuration: sp_staking::EraIndex = 24 * 7; // 1/4 the bonding duration.
	pub const RewardCurve: &'static PiecewiseLinear<'static> = &REWARD_CURVE;
	pub const MaxNominatorRewardedPerValidator: u32 = 256;
	pub OffchainRepeat: BlockNumber = 5;
	pub const MaxNominations: u32 = MAX_NOMINATIONS;
}

use frame_election_provider_support::onchain;
impl onchain::Config for Runtime {
	type Accuracy = Perbill;
	type DataProvider = Staking;
}

pub struct StakingBenchmarkingConfig;
impl pallet_staking::BenchmarkingConfig for StakingBenchmarkingConfig {
	type MaxNominators = ConstU32<1000>;
	type MaxValidators = ConstU32<1000>;
}

impl pallet_staking::Config for Runtime {
	type BenchmarkingConfig = StakingBenchmarkingConfig;
	type BondingDuration = BondingDuration;
	type Currency = Balances;
	type CurrencyToVote = U128CurrencyToVote;
	type ElectionProvider = ElectionProviderMultiPhase;
	type EraPayout = pallet_staking::ConvertCurve<RewardCurve>;
	type Event = Event;
	type GenesisElectionProvider = onchain::OnChainSequentialPhragmen<Self>;
	type MaxNominatorRewardedPerValidator = MaxNominatorRewardedPerValidator;
	type NextNewSession = Session;
	type OffendingValidatorsThreshold = OffendingValidatorsThreshold;
	// send the slashed funds to the treasury.
	type Reward = ();
	type RewardRemainder = Treasury;
	type SessionInterface = Self;
	// rewards are minted from the void
	type SessionsPerEra = SessionsPerEra;
	type Slash = Treasury;
	/// A super-majority of the council can cancel the slash.
	type SlashCancelOrigin = EnsureOneOf<
		EnsureRoot<AccountId>,
		pallet_collective::EnsureProportionAtLeast<_3, _4, AccountId, CouncilCollective>,
	>;
	type SlashDeferDuration = SlashDeferDuration;
	// Alternatively, use pallet_staking::UseNominatorsMap<Runtime> to just use the
	// nominators map. Note that the aforementioned does not scale to a very large
	// number of nominators.
	type SortedListProvider = BagsList;
	type UnixTime = Timestamp;
	type MaxNominations = MaxNominations;
	type WeightInfo = pallet_staking::weights::SubstrateWeight<Runtime>;
}

parameter_types! {
	// phase durations. 1/4 of the last session for each.
	pub const SignedPhase: u32 = EPOCH_DURATION_IN_BLOCKS / 4;
	pub const UnsignedPhase: u32 = EPOCH_DURATION_IN_BLOCKS / 4;

	// signed config
	pub const SignedMaxSubmissions: u32 = 10;
	pub const SignedRewardBase: Balance = 1 * DOLLARS;
	pub const SignedDepositBase: Balance = 1 * DOLLARS;
	pub const SignedDepositByte: Balance = 1 * CENTS;

	pub SolutionImprovementThreshold: Perbill = Perbill::from_rational(1u32, 10_000);

	// miner configs
	pub const MultiPhaseUnsignedPriority: TransactionPriority = StakingUnsignedPriority::get() - 1u64;
	pub MinerMaxWeight: Weight = RuntimeBlockWeights::get()
		.get(DispatchClass::Normal)
		.max_extrinsic.expect("Normal extrinsics have a weight limit configured; qed")
		.saturating_sub(BlockExecutionWeight::get());
	// Solution can occupy 90% of normal block size
	pub MinerMaxLength: u32 = Perbill::from_rational(9u32, 10) *
		*RuntimeBlockLength::get()
		.max
		.get(DispatchClass::Normal);

	// BagsList allows a practically unbounded count of nominators to participate in NPoS elections.
	// To ensure we respect memory limits when using the BagsList this must be set to a number of
	// voters we know can fit into a single vec allocation.
	pub const VoterSnapshotPerBlock: u32 = 10_000;
}

sp_npos_elections::generate_solution_type!(
	#[compact]
	pub struct NposSolution16::<
		VoterIndex = u32,
		TargetIndex = u16,
		Accuracy = sp_runtime::PerU16,
	>(16)
);

pub const MAX_NOMINATIONS: u32 = <NposSolution16 as sp_npos_elections::NposSolution>::LIMIT as u32;

/// The numbers configured here could always be more than the the maximum limits
/// of staking pallet to ensure election snapshot will not run out of memory.
/// For now, we set them to smaller values since the staking is bounded and the
/// weight pipeline takes hours for this single pallet.
pub struct BenchmarkConfig;
impl pallet_election_provider_multi_phase::BenchmarkingConfig for BenchmarkConfig {
	const ACTIVE_VOTERS: [u32; 2] = [500, 800];
	const DESIRED_TARGETS: [u32; 2] = [200, 400];
	const MAXIMUM_TARGETS: u32 = 300;
	const MINER_MAXIMUM_VOTERS: u32 = 1000;
	const SNAPSHOT_MAXIMUM_VOTERS: u32 = 1000;
	const TARGETS: [u32; 2] = [500, 1000];
	const VOTERS: [u32; 2] = [1000, 2000];
}

/// Maximum number of iterations for balancing that will be executed in the
/// embedded OCW miner of election provider multi phase.
pub const MINER_MAX_ITERATIONS: u32 = 10;

/// A source of random balance for NposSolver, which is meant to be run by the
/// OCW election miner.
pub struct OffchainRandomBalancing;
impl frame_support::pallet_prelude::Get<Option<(usize, sp_npos_elections::ExtendedBalance)>>
	for OffchainRandomBalancing
{
	fn get() -> Option<(usize, sp_npos_elections::ExtendedBalance)> {
		use sp_runtime::traits::TrailingZeroInput;
		let iters = match MINER_MAX_ITERATIONS {
			0 => 0,
			max => {
				let seed = sp_io::offchain::random_seed();
				let random = <u32>::decode(&mut TrailingZeroInput::new(&seed))
					.expect("input is padded with zeroes; qed") %
					max.saturating_add(1);
				random as usize
			},
		};

		Some((iters, 0))
	}
}

impl pallet_election_provider_multi_phase::Config for Runtime {
	type BenchmarkingConfig = BenchmarkConfig;
	type Currency = Balances;
	// nothing to do upon rewards
	type DataProvider = Staking;
	type EstimateCallFee = TransactionPayment;
	type Event = Event;
	type Fallback = pallet_election_provider_multi_phase::NoFallback<Self>;
	type ForceOrigin = EnsureRootOrHalfCouncil;
	type MinerMaxLength = MinerMaxLength;
	type MinerMaxWeight = MinerMaxWeight;
	type MinerTxPriority = MultiPhaseUnsignedPriority;
	type OffchainRepeat = OffchainRepeat;
	// burn slashes
	type RewardHandler = ();
	type SignedDepositBase = SignedDepositBase;
	type SignedDepositByte = SignedDepositByte;
	type SignedDepositWeight = ();
	type SignedMaxSubmissions = SignedMaxSubmissions;
	type SignedMaxWeight = MinerMaxWeight;
	type SignedPhase = SignedPhase;
	type SignedRewardBase = SignedRewardBase;
	type SlashHandler = ();
	type Solution = NposSolution16;
	type SolutionImprovementThreshold = SolutionImprovementThreshold;
	type Solver = frame_election_provider_support::SequentialPhragmen<
		AccountId,
		pallet_election_provider_multi_phase::SolutionAccuracyOf<Self>,
		OffchainRandomBalancing,
	>;
	type UnsignedPhase = UnsignedPhase;
	type VoterSnapshotPerBlock = VoterSnapshotPerBlock;
	type GovernanceFallback = NoFallback<Self>;
	type WeightInfo = pallet_election_provider_multi_phase::weights::SubstrateWeight<Self>;
}

parameter_types! {
	pub const BagThresholds: &'static [u64] = &voter_bags::THRESHOLDS;
}

impl pallet_bags_list::Config for Runtime {
	type BagThresholds = BagThresholds;
	type Event = Event;
	type VoteWeightProvider = Staking;
	type WeightInfo = pallet_bags_list::weights::SubstrateWeight<Runtime>;
}

parameter_types! {
	pub const LaunchPeriod: BlockNumber = 28 * 24 * 60 * MINUTES;
	pub const VotingPeriod: BlockNumber = 28 * 24 * 60 * MINUTES;
	pub const FastTrackVotingPeriod: BlockNumber = 3 * 24 * 60 * MINUTES;
	pub const InstantAllowed: bool = true;
	pub const MinimumDeposit: Balance = 100 * DOLLARS;
	pub const EnactmentPeriod: BlockNumber = 30 * 24 * 60 * MINUTES;
	pub const CooloffPeriod: BlockNumber = 28 * 24 * 60 * MINUTES;
	// One cent: $10,000 / MB
	pub const PreimageByteDeposit: Balance = 1 * CENTS;
	pub const MaxVotes: u32 = 100;
	pub const MaxProposals: u32 = 100;
}

type EnsureRootOrHalfCouncil = EnsureOneOf<
	EnsureRoot<AccountId>,
	pallet_collective::EnsureProportionMoreThan<_1, _2, AccountId, CouncilCollective>,
>;

impl pallet_democracy::Config for Runtime {
	type BlacklistOrigin = EnsureRoot<AccountId>;
	// To cancel a proposal before it has been passed, the technical committee must
	// be unanimous or Root must agree.
	type CancelProposalOrigin = EnsureOneOf<
		EnsureRoot<AccountId>,
		pallet_collective::EnsureProportionAtLeast<_1, _1, AccountId, CouncilCollective>,
	>;
	// To cancel a proposal which has been passed, 2/3 of the council must agree to
	// it.
	type CancellationOrigin =
		pallet_collective::EnsureProportionAtLeast<_2, _3, AccountId, CouncilCollective>;
	type CooloffPeriod = CooloffPeriod;
	type Currency = Balances;
	type EnactmentPeriod = EnactmentPeriod;
	type Event = Event;
	/// A unanimous council can have the next scheduled referendum be a straight
	/// default-carries (NTB) vote.
	type ExternalDefaultOrigin =
		pallet_collective::EnsureProportionAtLeast<_1, _1, AccountId, CouncilCollective>;
	/// A super-majority can have the next scheduled referendum be a straight
	/// majority-carries vote.
	type ExternalMajorityOrigin =
		pallet_collective::EnsureProportionAtLeast<_3, _4, AccountId, CouncilCollective>;
	/// A straight majority of the council can decide what their next motion is.
	type ExternalOrigin =
		pallet_collective::EnsureProportionAtLeast<_1, _2, AccountId, CouncilCollective>;
	/// Two thirds of the technical committee can have an
	/// ExternalMajority/ExternalDefault vote be tabled immediately and with a
	/// shorter voting/enactment period.
	type FastTrackOrigin =
		pallet_collective::EnsureProportionAtLeast<_2, _3, AccountId, CouncilCollective>;
	type FastTrackVotingPeriod = FastTrackVotingPeriod;
	type InstantAllowed = InstantAllowed;
	type InstantOrigin =
		pallet_collective::EnsureProportionAtLeast<_1, _1, AccountId, CouncilCollective>;
	type LaunchPeriod = LaunchPeriod;
	type MaxProposals = MaxProposals;
	type MaxVotes = MaxVotes;
	// Same as EnactmentPeriod
	type MinimumDeposit = MinimumDeposit;
	type OperationalPreimageOrigin = pallet_collective::EnsureMember<AccountId, CouncilCollective>;
	type PalletsOrigin = OriginCaller;
	type PreimageByteDeposit = PreimageByteDeposit;
	type Proposal = Call;
	type Scheduler = Scheduler;
	type Slash = Treasury;
	// Any single technical committee member may veto a coming council proposal,
	// however they can only do it once and it lasts only for the cool-off period.
	type VetoOrigin = pallet_collective::EnsureMember<AccountId, CouncilCollective>;
	type VoteLockingPeriod = EnactmentPeriod;
	type VotingPeriod = VotingPeriod;
	type WeightInfo = pallet_democracy::weights::SubstrateWeight<Runtime>;
}

parameter_types! {
	pub const CouncilMotionDuration: BlockNumber = 5 * DAYS;
	pub const CouncilMaxProposals: u32 = 100;
	pub const CouncilMaxMembers: u32 = 100;
}

type CouncilCollective = pallet_collective::Instance1;
impl pallet_collective::Config<CouncilCollective> for Runtime {
	type DefaultVote = pallet_collective::PrimeDefaultVote;
	type Event = Event;
	type MaxMembers = CouncilMaxMembers;
	type MaxProposals = CouncilMaxProposals;
	type MotionDuration = CouncilMotionDuration;
	type Origin = Origin;
	type Proposal = Call;
	type WeightInfo = pallet_collective::weights::SubstrateWeight<Runtime>;
}

parameter_types! {
	pub const CandidacyBond: Balance = 10 * DOLLARS;
	// 1 storage item created, key size is 32 bytes, value size is 16+16.
	pub const VotingBondBase: Balance = deposit(1, 64);
	// additional data per vote is 32 bytes (account id).
	pub const VotingBondFactor: Balance = deposit(0, 32);
	pub const TermDuration: BlockNumber = 7 * DAYS;
	pub const DesiredMembers: u32 = 13;
	pub const DesiredRunnersUp: u32 = 7;
	pub const ElectionsPhragmenPalletId: LockIdentifier = *b"phrelect";
}

// Make sure that there are no more than `MaxMembers` members elected via
// elections-phragmen.
const_assert!(DesiredMembers::get() <= CouncilMaxMembers::get());

impl pallet_elections_phragmen::Config for Runtime {
	type CandidacyBond = CandidacyBond;
	type ChangeMembers = Council;
	type Currency = Balances;
	type CurrencyToVote = U128CurrencyToVote;
	type DesiredMembers = DesiredMembers;
	type DesiredRunnersUp = DesiredRunnersUp;
	type Event = Event;
	// NOTE: this implies that council's genesis members cannot be set directly and
	// must come from this module.
	type InitializeMembers = Council;
	type KickedMember = ();
	type LoserCandidate = ();
	type PalletId = ElectionsPhragmenPalletId;
	type TermDuration = TermDuration;
	type VotingBondBase = VotingBondBase;
	type VotingBondFactor = VotingBondFactor;
	type WeightInfo = pallet_elections_phragmen::weights::SubstrateWeight<Runtime>;
}

parameter_types! {
	pub const ProposalBond: Permill = Permill::from_percent(5);
	pub const ProposalBondMinimum: Balance = 1 * DOLLARS;
	pub const SpendPeriod: BlockNumber = 1 * DAYS;
	pub const Burn: Permill = Permill::from_percent(50);
	pub const TipCountdown: BlockNumber = 1 * DAYS;
	pub const TipFindersFee: Percent = Percent::from_percent(20);
	pub const TipReportDepositBase: Balance = 1 * DOLLARS;
	pub const DataDepositPerByte: Balance = 1 * CENTS;
	pub const BountyDepositBase: Balance = 1 * DOLLARS;
	pub const BountyDepositPayoutDelay: BlockNumber = 1 * DAYS;
	pub const TreasuryPalletId: PalletId = PalletId(*b"py/trsry");
	pub const BountyUpdatePeriod: BlockNumber = 14 * DAYS;
	pub const MaximumReasonLength: u32 = 300;
	pub const BountyCuratorDeposit: Permill = Permill::from_percent(50);
	pub const BountyValueMinimum: Balance = 5 * DOLLARS;
	pub const MaxApprovals: u32 = 100;
	pub const MaxActiveChildBountyCount: u32 = 5;
	pub const ChildBountyValueMinimum: Balance = 1 * DOLLARS;
	pub const ChildBountyCuratorDepositBase: Permill = Permill::from_percent(10);
}

impl pallet_treasury::Config for Runtime {
	type ApproveOrigin = EnsureOneOf<
		EnsureRoot<AccountId>,
		pallet_collective::EnsureProportionAtLeast<_3, _5, AccountId, CouncilCollective>,
	>;
	type Burn = Burn;
	type BurnDestination = ();
	type Currency = Balances;
	type Event = Event;
	type MaxApprovals = MaxApprovals;
	type OnSlash = ();
	type PalletId = TreasuryPalletId;
	type ProposalBond = ProposalBond;
	type ProposalBondMinimum = ProposalBondMinimum;
	type RejectOrigin = EnsureOneOf<
		EnsureRoot<AccountId>,
		pallet_collective::EnsureProportionMoreThan<_1, _2, AccountId, CouncilCollective>,
	>;
	type SpendFunds = Bounties;
	type SpendPeriod = SpendPeriod;
	type ProposalBondMaximum = ();
	type WeightInfo = pallet_treasury::weights::SubstrateWeight<Runtime>;
}

impl pallet_bounties::Config for Runtime {
	type BountyCuratorDeposit = BountyCuratorDeposit;
	type BountyDepositBase = BountyDepositBase;
	type BountyDepositPayoutDelay = BountyDepositPayoutDelay;
	type BountyUpdatePeriod = BountyUpdatePeriod;
	type BountyValueMinimum = BountyValueMinimum;
	type ChildBountyManager = ChildBounties;
	type DataDepositPerByte = DataDepositPerByte;
	type Event = Event;
	type MaximumReasonLength = MaximumReasonLength;
	type WeightInfo = pallet_bounties::weights::SubstrateWeight<Runtime>;
}

impl pallet_child_bounties::Config for Runtime {
	type ChildBountyCuratorDepositBase = ChildBountyCuratorDepositBase;
	type ChildBountyValueMinimum = ChildBountyValueMinimum;
	type Event = Event;
	type MaxActiveChildBountyCount = MaxActiveChildBountyCount;
	type WeightInfo = pallet_child_bounties::weights::SubstrateWeight<Runtime>;
}

parameter_types! {
	// One storage item; key size is 32; value is size 4+4+16+32 bytes = 56 bytes.
	pub const DepositBase: Balance = deposit(1, 88);
	// Additional storage item size of 32 bytes.
	pub const DepositFactor: Balance = deposit(0, 32);
	pub const MaxSignatories: u16 = 100;
}

impl pallet_multisig::Config for Runtime {
	type Call = Call;
	type Currency = Balances;
	type DepositBase = DepositBase;
	type DepositFactor = DepositFactor;
	type Event = Event;
	type MaxSignatories = MaxSignatories;
	type WeightInfo = weights::pallet_multisig::WeightInfo<Runtime>;
}

impl pallet_utility::Config for Runtime {
	type Call = Call;
	type Event = Event;
	type PalletsOrigin = OriginCaller;
	type WeightInfo = weights::pallet_utility::WeightInfo<Runtime>;
}

parameter_types! {
	// One storage item; key size 32, value size 8; .
	pub const ProxyDepositBase: Balance = deposit(1, 40);
	// Additional storage item size of 33 bytes.
	pub const ProxyDepositFactor: Balance = deposit(0, 33);
	pub const MaxProxies: u16 = 32;
	// One storage item; key size 32, value size 16
	pub const AnnouncementDepositBase: Balance = deposit(1, 48);
	pub const AnnouncementDepositFactor: Balance = deposit(0, 66);
	pub const MaxPending: u16 = 32;
}

/// The type used to represent the kinds of proxying allowed.
#[derive(
	Copy,
	Clone,
	Eq,
	PartialEq,
	Ord,
	PartialOrd,
	Encode,
	Decode,
	RuntimeDebug,
	MaxEncodedLen,
	scale_info::TypeInfo,
)]
pub enum ProxyType {
	/// Fully permissioned proxy. Can execute any call on behalf of _proxied_.
	Any,
	/// Can execute any call that does not transfer funds or assets.
	NonTransfer,
	/// Proxy with the ability to reject time-delay proxy announcements.
	CancelProxy,
	/// Assets proxy. Can execute any call from `assets`, **including asset
	/// transfers**.
	Assets,
	/// Owner proxy. Can execute calls related to asset ownership.
	AssetOwner,
	/// Asset manager. Can execute calls related to asset management.
	AssetManager,
}
impl Default for ProxyType {
	fn default() -> Self {
		Self::Any
	}
}
impl InstanceFilter<Call> for ProxyType {
	fn filter(&self, c: &Call) -> bool {
		match self {
			ProxyType::Any => true,
			ProxyType::NonTransfer => !matches!(c, Call::Balances { .. } | Call::Assets { .. }),
			ProxyType::CancelProxy => matches!(
				c,
				Call::Proxy(pallet_proxy::Call::reject_announcement { .. }) |
					Call::Utility { .. } | Call::Multisig { .. }
			),
			ProxyType::Assets => {
				matches!(c, Call::Assets { .. } | Call::Utility { .. } | Call::Multisig { .. })
			},
			ProxyType::AssetOwner => matches!(
				c,
				Call::Assets(pallet_assets::Call::create { .. }) |
					Call::Assets(pallet_assets::Call::destroy { .. }) |
					Call::Assets(pallet_assets::Call::transfer_ownership { .. }) |
					Call::Assets(pallet_assets::Call::set_team { .. }) |
					Call::Assets(pallet_assets::Call::set_metadata { .. }) |
					Call::Assets(pallet_assets::Call::clear_metadata { .. }) |
					Call::Utility { .. } | Call::Multisig { .. }
			),
			ProxyType::AssetManager => matches!(
				c,
				Call::Assets(pallet_assets::Call::mint { .. }) |
					Call::Assets(pallet_assets::Call::burn { .. }) |
					Call::Assets(pallet_assets::Call::freeze { .. }) |
					Call::Assets(pallet_assets::Call::thaw { .. }) |
					Call::Assets(pallet_assets::Call::freeze_asset { .. }) |
					Call::Assets(pallet_assets::Call::thaw_asset { .. }) |
					Call::Utility { .. } | Call::Multisig { .. }
			),
		}
	}

	fn is_superset(&self, o: &Self) -> bool {
		match (self, o) {
			(x, y) if x == y => true,
			(ProxyType::Any, _) => true,
			(_, ProxyType::Any) => false,
			(ProxyType::Assets, ProxyType::AssetOwner) => true,
			(ProxyType::Assets, ProxyType::AssetManager) => true,
			_ => false,
		}
	}
}

impl pallet_proxy::Config for Runtime {
	type AnnouncementDepositBase = AnnouncementDepositBase;
	type AnnouncementDepositFactor = AnnouncementDepositFactor;
	type Call = Call;
	type CallHasher = BlakeTwo256;
	type Currency = Balances;
	type Event = Event;
	type MaxPending = MaxPending;
	type MaxProxies = MaxProxies;
	type ProxyDepositBase = ProxyDepositBase;
	type ProxyDepositFactor = ProxyDepositFactor;
	type ProxyType = ProxyType;
	type WeightInfo = weights::pallet_proxy::WeightInfo<Runtime>;
}

parameter_types! {
	pub const AssetDeposit: Balance = UNITS; // 1 UNIT deposit to create asset
	pub const ApprovalDeposit: Balance = EXISTENTIAL_DEPOSIT;
	pub const AssetsStringLimit: u32 = 50;
	/// Key = 32 bytes, Value = 36 bytes (32+1+1+1+1)
	// https://github.com/paritytech/substrate/blob/069917b/frame/assets/src/lib.rs#L257L271
	pub const MetadataDepositBase: Balance = deposit(1, 68);
	pub const MetadataDepositPerByte: Balance = deposit(0, 1);
}

/// We allow root and the Relay Chain council to execute privileged asset
/// operations.
pub type AssetsForceOrigin = EnsureRoot<AccountId>;

impl pallet_assets::Config for Runtime {
	type ApprovalDeposit = ApprovalDeposit;
	type AssetAccountDeposit = ConstU128<DOLLARS>;
	type AssetDeposit = AssetDeposit;
	type AssetId = u32;
	type Balance = u128;
	type Currency = Balances;
	type Event = Event;
	type Extra = ();
	type ForceOrigin = EnsureRoot<AccountId>;
	type Freezer = ();
	type MetadataDepositBase = MetadataDepositBase;
	type MetadataDepositPerByte = MetadataDepositPerByte;
	type StringLimit = StringLimit;
	type WeightInfo = pallet_assets::weights::SubstrateWeight<Runtime>;
}

impl pallet_sudo::Config for Runtime {
	type Call = Call;
	type Event = Event;
}

parameter_types! {
	pub const ImOnlineUnsignedPriority: TransactionPriority = TransactionPriority::max_value();
	/// We prioritize im-online heartbeats over election solution submission.
	pub const StakingUnsignedPriority: TransactionPriority = TransactionPriority::max_value() / 2;
	pub const MaxAuthorities: u32 = 100;
	pub const MaxKeys: u32 = 10_000;
	pub const MaxPeerInHeartbeats: u32 = 10_000;
	pub const MaxPeerDataEncodingSize: u32 = 1_000;
}

impl<LocalCall> frame_system::offchain::CreateSignedTransaction<LocalCall> for Runtime
where
	Call: From<LocalCall>,
{
	fn create_transaction<C: frame_system::offchain::AppCrypto<Self::Public, Self::Signature>>(
		call: Call,
		public: <Signature as traits::Verify>::Signer,
		account: AccountId,
		nonce: Index,
	) -> Option<(Call, <UncheckedExtrinsic as traits::Extrinsic>::SignaturePayload)> {
		let tip = 0;
		// take the biggest period possible.
		let period =
			BlockHashCount::get().checked_next_power_of_two().map(|c| c / 2).unwrap_or(2) as u64;
		let current_block = System::block_number()
			.saturated_into::<u64>()
			// The `System::block_number` is initialized with `n+1`,
			// so the actual block number is `n`.
			.saturating_sub(1);
		let era = Era::mortal(period, current_block);
		let extra = (
			frame_system::CheckSpecVersion::<Runtime>::new(),
			frame_system::CheckTxVersion::<Runtime>::new(),
			frame_system::CheckGenesis::<Runtime>::new(),
			frame_system::CheckEra::<Runtime>::from(era),
			frame_system::CheckNonce::<Runtime>::from(nonce),
			frame_system::CheckWeight::<Runtime>::new(),
			pallet_transaction_payment::ChargeTransactionPayment::<Runtime>::from(tip),
		);
		let raw_payload = SignedPayload::new(call, extra)
			.map_err(|e| {
				log::warn!("Unable to create signed payload: {:?}", e);
			})
			.ok()?;
		let signature = raw_payload.using_encoded(|payload| C::sign(payload, public))?;
		let address = Indices::unlookup(account);
		let (call, extra, _) = raw_payload.deconstruct();
		Some((call, (address, signature, extra)))
	}
}

impl frame_system::offchain::SigningTypes for Runtime {
	type Public = <Signature as traits::Verify>::Signer;
	type Signature = Signature;
}

impl<C> frame_system::offchain::SendTransactionTypes<C> for Runtime
where
	Call: From<C>,
{
	type Extrinsic = UncheckedExtrinsic;
	type OverarchingCall = Call;
}

impl pallet_im_online::Config for Runtime {
	type AuthorityId = ImOnlineId;
	type Event = Event;
	type MaxKeys = MaxKeys;
	type MaxPeerDataEncodingSize = MaxPeerDataEncodingSize;
	type MaxPeerInHeartbeats = MaxPeerInHeartbeats;
	type NextSessionRotation = Babe;
	type ReportUnresponsiveness = Offences;
	type UnsignedPriority = ImOnlineUnsignedPriority;
	type ValidatorSet = Historical;
	type WeightInfo = pallet_im_online::weights::SubstrateWeight<Runtime>;
}

impl pallet_offences::Config for Runtime {
	type Event = Event;
	type IdentificationTuple = pallet_session::historical::IdentificationTuple<Self>;
	type OnOffenceHandler = Staking;
}

impl pallet_authority_discovery::Config for Runtime {
	type MaxAuthorities = MaxAuthorities;
}

impl pallet_grandpa::Config for Runtime {
	type Call = Call;
	type Event = Event;
	type HandleEquivocation = pallet_grandpa::EquivocationHandler<
		Self::KeyOwnerIdentification,
		Offences,
		ReportLongevity,
	>;
	type KeyOwnerIdentification = <Self::KeyOwnerProofSystem as KeyOwnerProofSystem<(
		KeyTypeId,
		GrandpaId,
	)>>::IdentificationTuple;
	type KeyOwnerProof =
		<Self::KeyOwnerProofSystem as KeyOwnerProofSystem<(KeyTypeId, GrandpaId)>>::Proof;
	type KeyOwnerProofSystem = Historical;
	type MaxAuthorities = MaxAuthorities;
	type WeightInfo = ();
}

parameter_types! {
	pub const StringLimit: u32 = 50;
}

impl pallet_hasher::Config<pallet_hasher::Instance1> for Runtime {
	type Event = Event;
	type ForceOrigin = frame_system::EnsureRoot<AccountId>;
	type Hasher = ArkworksPoseidonHasherBn254;
	type WeightInfo = pallet_hasher::weights::WebbWeight<Runtime>;
}

impl pallet_randomness_collective_flip::Config for Runtime {}

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

#[derive(Debug, Encode, Decode, Default, Copy, Clone, PartialEq, Eq, scale_info::TypeInfo)]
#[cfg_attr(feature = "std", derive(Serialize, Deserialize))]
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

impl pallet_mt::Config<pallet_mt::Instance1> for Runtime {
	type Currency = Balances;
	type DataDepositBase = LeafDepositBase;
	type DataDepositPerByte = LeafDepositPerByte;
	type DefaultZeroElement = NewDefaultZeroElement;
	type Element = Element;
	type Event = Event;
	type ForceOrigin = frame_system::EnsureRoot<AccountId>;
	type Hasher = HasherBn254;
	type LeafIndex = u32;
	type MaxTreeDepth = MaxTreeDepth;
	type RootHistorySize = RootHistorySize;
	type RootIndex = u32;
	type StringLimit = StringLimit;
	type TreeDeposit = TreeDeposit;
	type TreeId = u32;
	type Two = Two;
	type WeightInfo = pallet_mt::weights::WebbWeight<Runtime>;
}

impl pallet_verifier::Config<pallet_verifier::Instance1> for Runtime {
	type Event = Event;
	type ForceOrigin = frame_system::EnsureRoot<AccountId>;
	type Verifier = ArkworksVerifierBn254;
	type WeightInfo = pallet_verifier::weights::WebbWeight<Runtime>;
}

impl pallet_verifier::Config<pallet_verifier::Instance2> for Runtime {
	type Event = Event;
	type ForceOrigin = frame_system::EnsureRoot<AccountId>;
	type Verifier = ArkworksVerifierBn254;
	type WeightInfo = pallet_verifier::weights::WebbWeight<Runtime>;
}

impl pallet_verifier::Config<pallet_verifier::Instance3> for Runtime {
	type Event = Event;
	type ForceOrigin = frame_system::EnsureRoot<AccountId>;
	type Verifier = ArkworksVerifierBn254;
	type WeightInfo = pallet_verifier::weights::WebbWeight<Runtime>;
}

impl pallet_asset_registry::Config for Runtime {
	type AssetId = webb_primitives::AssetId;
	type AssetNativeLocation = ();
	type Balance = Balance;
	type Event = Event;
	type NativeAssetId = NativeCurrencyId;
	type RegistryOrigin = frame_system::EnsureRoot<AccountId>;
	type StringLimit = RegistryStringLimit;
	type WeightInfo = ();
}

impl orml_tokens::Config for Runtime {
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

impl orml_currencies::Config for Runtime {
	type Event = Event;
	type GetNativeCurrencyId = NativeCurrencyId;
	type MultiCurrency = Tokens;
	type NativeCurrency = BasicCurrencyAdapter<Runtime, Balances, Amount, BlockNumber>;
	type WeightInfo = ();
}

parameter_types! {
	pub const MixerPalletId: PalletId = PalletId(*b"py/mixer");
	pub const NativeCurrencyId: webb_primitives::AssetId = 0;
	pub const RegistryStringLimit: u32 = 10;
}

impl pallet_mixer::Config<pallet_mixer::Instance1> for Runtime {
	type Currency = Currencies;
	type Event = Event;
	type NativeCurrencyId = NativeCurrencyId;
	type PalletId = MixerPalletId;
	type Tree = MerkleTreeBn254;
	type Verifier = MixerVerifierBn254;
	type ArbitraryHasher = Keccak256HasherBn254;
	type WeightInfo = pallet_mixer::weights::WebbWeight<Runtime>;
}

parameter_types! {
	pub const AnchorPalletId: PalletId = PalletId(*b"py/anchr");
	pub const HistoryLength: u32 = 30;
	// Substrate standalone chain ID type
	pub const ChainType: [u8; 2] = [2, 0];
	pub const ChainIdentifier: ChainId = 1080;
}

impl pallet_linkable_tree::Config<pallet_linkable_tree::Instance1> for Runtime {
	type ChainId = ChainId;
	type ChainType = ChainType;
	type ChainIdentifier = ChainIdentifier;
	type Event = Event;
	type HistoryLength = HistoryLength;
	type Tree = MerkleTreeBn254;
	type WeightInfo = ();
}

impl pallet_anchor::Config<pallet_anchor::Instance1> for Runtime {
	type Currency = Currencies;
	type Event = Event;
	type LinkableTree = LinkableTreeBn254;
	type NativeCurrencyId = NativeCurrencyId;
	type PalletId = AnchorPalletId;
	type PostDepositHook = ();
	type Verifier = AnchorVerifierBn254;
	type ArbitraryHasher = Keccak256HasherBn254;
	type WeightInfo = pallet_anchor::weights::WebbWeight<Runtime>;
}

impl pallet_anchor_handler::Config<pallet_anchor_handler::Instance1> for Runtime {
	type Anchor = AnchorBn254;
	type BridgeOrigin = pallet_bridge::EnsureBridge<Runtime, BridgeInstance>;
	type Event = Event;
}

parameter_types! {
	pub const VAnchorPalletId: PalletId = PalletId(*b"py/vanch");
	pub const MaxFee: Balance = Balance::MAX - 1;
	pub const MaxExtAmount: Balance = Balance::MAX - 1;
}

impl pallet_vanchor::Config<pallet_vanchor::Instance1> for Runtime {
	type Event = Event;
	type PalletId = VAnchorPalletId;
	type LinkableTree = LinkableTreeBn254;
	type Verifier2x2 = VAnchorVerifier2x2Bn254;
	type EthereumHasher = Keccak256HasherBn254;
	type IntoField = ArkworksIntoFieldBn254;
	type Currency = Currencies;
	type MaxFee = MaxFee;
	type MaxExtAmount = MaxExtAmount;
	type PostDepositHook = ();
	type NativeCurrencyId = NativeCurrencyId;
}

parameter_types! {
	pub const ProposalLifetime: BlockNumber = 50;
	pub const BridgeAccountId: PalletId = PalletId(*b"dw/bridg");
}

type BridgeInstance = pallet_bridge::Instance1;
impl pallet_bridge::Config<BridgeInstance> for Runtime {
	type AdminOrigin = frame_system::EnsureRoot<Self::AccountId>;
	type BridgeAccountId = BridgeAccountId;
	type ChainId = ChainId;
	type ChainIdentifier = ChainIdentifier;
	type ChainType = ChainType;
	type Event = Event;
	type Proposal = Call;
	type ProposalLifetime = ProposalLifetime;
}

parameter_types! {
	pub const TokenWrapperPalletId: PalletId = PalletId(*b"dw/tkwrp");
	pub const WrappingFeeDivider: Balance = 100;
}

impl pallet_token_wrapper::Config for Runtime {
	type AssetRegistry = AssetRegistry;
	type Currency = Currencies;
	type Event = Event;
	type PalletId = TokenWrapperPalletId;
	type TreasuryId = TreasuryPalletId;
	type WeightInfo = pallet_token_wrapper::weights::WebbWeight<Runtime>;
	type WrappingFeeDivider = WrappingFeeDivider;
}

// Create the runtime by composing the FRAME pallets that were previously
// configured.
construct_runtime!(
	pub enum Runtime where
		Block = Block,
		NodeBlock = opaque::Block,
		UncheckedExtrinsic = UncheckedExtrinsic
	{
		// System support stuff.
		System: frame_system::{Pallet, Call, Config, Storage, Event<T>},
		RandomnessCollectiveFlip: pallet_randomness_collective_flip::{Pallet, Storage},
		Timestamp: pallet_timestamp::{Pallet, Call, Storage, Inherent},
		Babe: pallet_babe::{Pallet, Call, Storage, Config, ValidateUnsigned},

		Authorship: pallet_authorship::{Pallet, Call, Storage},
		Indices: pallet_indices::{Pallet, Call, Storage, Config<T>, Event<T>},

		Balances: pallet_balances::{Pallet, Call, Storage, Config<T>, Event<T>},
		TransactionPayment: pallet_transaction_payment::{Pallet, Storage},
		ElectionProviderMultiPhase: pallet_election_provider_multi_phase::{Pallet, Call, Storage, Event<T>, ValidateUnsigned},
		Staking: pallet_staking::{Pallet, Call, Config<T>, Storage, Event<T>},
		Session: pallet_session::{Pallet, Call, Storage, Event, Config<T>},
		Democracy: pallet_democracy::{Pallet, Call, Storage, Config<T>, Event<T>},
		Council: pallet_collective::<Instance1>::{Pallet, Call, Storage, Origin<T>, Event<T>, Config<T>},
		Elections: pallet_elections_phragmen::{Pallet, Call, Storage, Event<T>, Config<T>},
		Grandpa: pallet_grandpa::{Pallet, Call, Storage, Config, Event, ValidateUnsigned},
		Treasury: pallet_treasury::{Pallet, Call, Storage, Config, Event<T>},

		Utility: pallet_utility::{Pallet, Call, Event},
		Multisig: pallet_multisig::{Pallet, Call, Storage, Event<T>},
		Scheduler: pallet_scheduler::{Pallet, Call, Storage, Event<T>},
		Preimage: pallet_preimage::{Pallet, Call, Storage, Event<T>},
		Proxy: pallet_proxy::{Pallet, Call, Storage, Event<T>},

		// The main stage. To include pallet-assets-freezer and pallet-uniques.
		Assets: pallet_assets::{Pallet, Call, Storage, Event<T>},
		Sudo: pallet_sudo::{Pallet, Call, Config<T>, Storage, Event<T>},
		ImOnline: pallet_im_online::{Pallet, Call, Storage, Event<T>, ValidateUnsigned, Config<T>},
		AuthorityDiscovery: pallet_authority_discovery::{Pallet, Config},
		Offences: pallet_offences::{Pallet, Storage, Event},
		Historical: pallet_session_historical::{Pallet},
		Bounties: pallet_bounties::{Pallet, Call, Storage, Event<T>},
		ChildBounties: pallet_child_bounties::{Pallet, Call, Storage, Event<T>},
		BagsList: pallet_bags_list::{Pallet, Call, Storage, Event<T>},

		// Hasher pallet
		HasherBn254: pallet_hasher::<Instance1>::{Pallet, Call, Storage, Event<T>, Config<T>},

		AssetRegistry: pallet_asset_registry::{Pallet, Call, Storage, Event<T>, Config<T>},
		Currencies: orml_currencies::{Pallet, Call, Event<T>},
		Tokens: orml_tokens::{Pallet, Storage, Call, Event<T>},
		TokenWrapper: pallet_token_wrapper::{Pallet, Storage, Call, Event<T>},

		// Mixer Verifier
		MixerVerifierBn254: pallet_verifier::<Instance1>::{Pallet, Call, Storage, Event<T>, Config<T>},

		// Anchor Verifier
		AnchorVerifierBn254: pallet_verifier::<Instance2>::{Pallet, Call, Storage, Event<T>, Config<T>},

		// VAnchor Verifier 2x2
		VAnchorVerifier2x2Bn254: pallet_verifier::<Instance3>::{Pallet, Call, Storage, Event<T>, Config<T>},

		// Merkle Tree
		MerkleTreeBn254: pallet_mt::<Instance1>::{Pallet, Call, Storage, Event<T>, Config<T>},

		// Linkable Merkle Tree
		LinkableTreeBn254: pallet_linkable_tree::<Instance1>::{Pallet, Call, Storage, Event<T>},

		// Mixer
		MixerBn254: pallet_mixer::<Instance1>::{Pallet, Call, Storage, Event<T>, Config<T>},

		// Anchor
		AnchorBn254: pallet_anchor::<Instance1>::{Pallet, Call, Storage, Event<T>, Config<T>},

		// Anchor Handler
		AnchorHandlerBn254: pallet_anchor_handler::<Instance1>::{Pallet, Call, Storage, Event<T>},

		// VAnchor
		VAnchorBn254: pallet_vanchor::<Instance1>::{Pallet, Call, Storage, Event<T>, Config<T>},

		Bridge: pallet_bridge::<Instance1>::{Pallet, Call, Storage, Event<T>},
	}
);

/// The address format for describing accounts.
pub type Address = sp_runtime::MultiAddress<AccountId, AccountIndex>;
/// Block header type as expected by this runtime.
pub type Header = generic::Header<BlockNumber, BlakeTwo256>;
/// Block type as expected by this runtime.
pub type Block = generic::Block<Header, UncheckedExtrinsic>;
/// A Block signed with a Justification
pub type SignedBlock = generic::SignedBlock<Block>;
/// BlockId type as expected by this runtime.
pub type BlockId = generic::BlockId<Block>;
/// The SignedExtension to the basic transaction logic.
///
/// When you change this, you **MUST** modify [`sign`] in
/// `bin/node/testing/src/keyring.rs`!
///
/// [`sign`]: <../../testing/src/keyring.rs.html>
pub type SignedExtra = (
	frame_system::CheckSpecVersion<Runtime>,
	frame_system::CheckTxVersion<Runtime>,
	frame_system::CheckGenesis<Runtime>,
	frame_system::CheckEra<Runtime>,
	frame_system::CheckNonce<Runtime>,
	frame_system::CheckWeight<Runtime>,
	pallet_transaction_payment::ChargeTransactionPayment<Runtime>,
);
/// Unchecked extrinsic type as expected by this runtime.
pub type UncheckedExtrinsic = generic::UncheckedExtrinsic<Address, Call, Signature, SignedExtra>;
/// The payload being signed in transactions.
pub type SignedPayload = generic::SignedPayload<Call, SignedExtra>;
/// Extrinsic type that has already been checked.
pub type CheckedExtrinsic = generic::CheckedExtrinsic<AccountId, Call, SignedExtra>;
/// Executive: handles dispatch to the various modules.
pub type Executive = frame_executive::Executive<
	Runtime,
	Block,
	frame_system::ChainContext<Runtime>,
	Runtime,
	AllPalletsWithoutSystemReversed,
	OnRuntimeUpgrade,
>;

pub struct OnRuntimeUpgrade;
impl frame_support::traits::OnRuntimeUpgrade for OnRuntimeUpgrade {
	fn on_runtime_upgrade() -> u64 {
		frame_support::migrations::migrate_from_pallet_version_to_storage_version::<
			AllPalletsWithSystem,
		>(&RocksDbWeight::get())
	}
}

impl_runtime_apis! {
	impl sp_api::Core<Block> for Runtime {
		fn version() -> RuntimeVersion {
			VERSION
		}

		fn execute_block(block: Block) {
			Executive::execute_block(block)
		}

		fn initialize_block(header: &<Block as BlockT>::Header) {
			Executive::initialize_block(header)
		}
	}

	impl sp_api::Metadata<Block> for Runtime {
		fn metadata() -> OpaqueMetadata {
			OpaqueMetadata::new(Runtime::metadata().into())
		}
	}

	impl sp_block_builder::BlockBuilder<Block> for Runtime {
		fn apply_extrinsic(extrinsic: <Block as BlockT>::Extrinsic) -> ApplyExtrinsicResult {
			Executive::apply_extrinsic(extrinsic)
		}

		fn finalize_block() -> <Block as BlockT>::Header {
			Executive::finalize_block()
		}

		fn inherent_extrinsics(data: sp_inherents::InherentData) -> Vec<<Block as BlockT>::Extrinsic> {
			data.create_extrinsics()
		}

		fn check_inherents(
			block: Block,
			data: sp_inherents::InherentData,
		) -> sp_inherents::CheckInherentsResult {
			data.check_extrinsics(&block)
		}
	}

	impl sp_transaction_pool::runtime_api::TaggedTransactionQueue<Block> for Runtime {
		fn validate_transaction(
			source: TransactionSource,
			tx: <Block as BlockT>::Extrinsic,
			block_hash: <Block as BlockT>::Hash,
		) -> TransactionValidity {
			Executive::validate_transaction(source, tx, block_hash)
		}
	}

	impl sp_offchain::OffchainWorkerApi<Block> for Runtime {
		fn offchain_worker(header: &<Block as BlockT>::Header) {
			Executive::offchain_worker(header)
		}
	}

	impl fg_primitives::GrandpaApi<Block> for Runtime {
		fn grandpa_authorities() -> GrandpaAuthorityList {
			Grandpa::grandpa_authorities()
		}

		fn current_set_id() -> fg_primitives::SetId {
			Grandpa::current_set_id()
		}

		fn submit_report_equivocation_unsigned_extrinsic(
			equivocation_proof: fg_primitives::EquivocationProof<
				<Block as BlockT>::Hash,
				NumberFor<Block>,
			>,
			key_owner_proof: fg_primitives::OpaqueKeyOwnershipProof,
		) -> Option<()> {
			let key_owner_proof = key_owner_proof.decode()?;

			Grandpa::submit_unsigned_equivocation_report(
				equivocation_proof,
				key_owner_proof,
			)
		}

		fn generate_key_ownership_proof(
			_set_id: fg_primitives::SetId,
			authority_id: GrandpaId,
		) -> Option<fg_primitives::OpaqueKeyOwnershipProof> {
			use codec::Encode;

			Historical::prove((fg_primitives::KEY_TYPE, authority_id))
				.map(|p| p.encode())
				.map(fg_primitives::OpaqueKeyOwnershipProof::new)
		}
	}

	impl sp_consensus_babe::BabeApi<Block> for Runtime {
		fn configuration() -> sp_consensus_babe::BabeGenesisConfiguration {
			// The choice of `c` parameter (where `1 - c` represents the
			// probability of a slot being empty), is done in accordance to the
			// slot duration and expected target block time, for safely
			// resisting network delays of maximum two seconds.
			// <https://research.web3.foundation/en/latest/polkadot/BABE/Babe/#6-practical-results>
			sp_consensus_babe::BabeGenesisConfiguration {
				slot_duration: Babe::slot_duration(),
				epoch_length: EpochDuration::get(),
				c: BABE_GENESIS_EPOCH_CONFIG.c,
				genesis_authorities: Babe::authorities().to_vec(),
				randomness: Babe::randomness(),
				allowed_slots: BABE_GENESIS_EPOCH_CONFIG.allowed_slots,
			}
		}

		fn current_epoch_start() -> sp_consensus_babe::Slot {
			Babe::current_epoch_start()
		}

		fn current_epoch() -> sp_consensus_babe::Epoch {
			Babe::current_epoch()
		}

		fn next_epoch() -> sp_consensus_babe::Epoch {
			Babe::next_epoch()
		}

		fn generate_key_ownership_proof(
			_slot: sp_consensus_babe::Slot,
			authority_id: sp_consensus_babe::AuthorityId,
		) -> Option<sp_consensus_babe::OpaqueKeyOwnershipProof> {
			use codec::Encode;

			Historical::prove((sp_consensus_babe::KEY_TYPE, authority_id))
				.map(|p| p.encode())
				.map(sp_consensus_babe::OpaqueKeyOwnershipProof::new)
		}

		fn submit_report_equivocation_unsigned_extrinsic(
			equivocation_proof: sp_consensus_babe::EquivocationProof<<Block as BlockT>::Header>,
			key_owner_proof: sp_consensus_babe::OpaqueKeyOwnershipProof,
		) -> Option<()> {
			let key_owner_proof = key_owner_proof.decode()?;

			Babe::submit_unsigned_equivocation_report(
				equivocation_proof,
				key_owner_proof,
			)
		}
	}

	impl sp_authority_discovery::AuthorityDiscoveryApi<Block> for Runtime {
		fn authorities() -> Vec<AuthorityDiscoveryId> {
			AuthorityDiscovery::authorities()
		}
	}

	impl frame_system_rpc_runtime_api::AccountNonceApi<Block, AccountId, Index> for Runtime {
		fn account_nonce(account: AccountId) -> Index {
			System::account_nonce(account)
		}
	}

	impl pallet_transaction_payment_rpc_runtime_api::TransactionPaymentApi<
		Block,
		Balance,
	> for Runtime {
		fn query_info(uxt: <Block as BlockT>::Extrinsic, len: u32) -> RuntimeDispatchInfo<Balance> {
			TransactionPayment::query_info(uxt, len)
		}
		fn query_fee_details(uxt: <Block as BlockT>::Extrinsic, len: u32) -> FeeDetails<Balance> {
			TransactionPayment::query_fee_details(uxt, len)
		}
	}

	impl sp_session::SessionKeys<Block> for Runtime {
		fn generate_session_keys(seed: Option<Vec<u8>>) -> Vec<u8> {
			SessionKeys::generate(seed)
		}

		fn decode_session_keys(
			encoded: Vec<u8>,
		) -> Option<Vec<(Vec<u8>, KeyTypeId)>> {
			SessionKeys::decode_into_raw_public_keys(&encoded)
		}
	}

	impl pallet_mt_rpc_runtime_api::MerkleTreeApi<Block, Element> for Runtime {
		fn get_leaf(tree_id: u32, index: u32) -> Option<Element> {
			let v = MerkleTreeBn254::leaves(tree_id, index);
			if v == Element::default() {
				None
			} else {
				Some(v)
			}
		}
	}

	#[cfg(feature = "runtime-benchmarks")]
	impl frame_benchmarking::Benchmark<Block> for Runtime {
		fn benchmark_metadata(extra: bool) -> (
			Vec<frame_benchmarking::BenchmarkList>,
			Vec<frame_support::traits::StorageInfo>,
		) {
			use frame_benchmarking::{list_benchmark, Benchmarking, BenchmarkList};
			use frame_support::traits::StorageInfoTrait;

			let mut list = Vec::<BenchmarkList>::new();

			list_benchmark!(list, extra, pallet_hasher, HasherBn254);
			list_benchmark!(list, extra, pallet_mt, MerkleTreeBn254);
			list_benchmark!(list, extra, pallet_linkable_tree, LinkableTreeBn254);
			list_benchmark!(list, extra, pallet_vanchor, VAnchorBn254);
			list_benchmark!(list, extra, pallet_anchor, AnchorBn254);
			list_benchmark!(list, extra, pallet_mixer, MixerBn254);
			list_benchmark!(list, extra, pallet_verifier, MixerVerifierBn254);
			list_benchmark!(list, extra, pallet_verifier, AnchorVerifierBn254);
			list_benchmark!(list, extra, pallet_token_wrapper, TokenWrapper);

			let storage_info = AllPalletsWithSystem::storage_info();

			return (list, storage_info)
		}

		fn dispatch_benchmark(
			config: frame_benchmarking::BenchmarkConfig
		) -> Result<Vec<frame_benchmarking::BenchmarkBatch>, sp_runtime::RuntimeString> {
			use frame_benchmarking::{Benchmarking, BenchmarkBatch, add_benchmark, TrackedStorageKey};

			impl frame_system_benchmarking::Config for Runtime {}

			let whitelist: Vec<TrackedStorageKey> = vec![
				// Block Number
				hex_literal::hex!("26aa394eea5630e07c48ae0c9558cef702a5c1b19ab7a04f536c519aca4983ac").to_vec().into(),
				// Total Issuance
				hex_literal::hex!("c2261276cc9d1f8598ea4b6a74b15c2f57c875e4cff74148e4628f264b974c80").to_vec().into(),
				// Execution Phase
				hex_literal::hex!("26aa394eea5630e07c48ae0c9558cef7ff553b5a9862a516939d82b3d3d8661a").to_vec().into(),
				// Event Count
				hex_literal::hex!("26aa394eea5630e07c48ae0c9558cef70a98fdbe9ce6c55837576c60c7af3850").to_vec().into(),
				// System Events
				hex_literal::hex!("26aa394eea5630e07c48ae0c9558cef780d41e5e16056765bc8461851072c9d7").to_vec().into(),
			];

			let mut batches = Vec::<BenchmarkBatch>::new();
			let params = (&config, &whitelist);

			add_benchmark!(params, batches, pallet_hasher, HasherBn254);
			add_benchmark!(params, batches, pallet_mt, MerkleTreeBn254);
			add_benchmark!(params, batches, pallet_linkable_tree, LinkableTreeBn254);
			add_benchmark!(params, batches, pallet_vanchor, VAnchorBn254);
			add_benchmark!(params, batches, pallet_anchor, AnchorBn254);
			add_benchmark!(params, batches, pallet_mixer, MixerBn254);
			add_benchmark!(params, batches, pallet_mixer, MixerBls254);
			add_benchmark!(params, batches, pallet_verifier, MixerVerifierBn254);
			add_benchmark!(params, batches, pallet_verifier, AnchorVerifierBn254);
			add_benchmark!(params, batches, pallet_token_wrapper, TokenWrapper);

			if batches.is_empty() { return Err("Benchmark not found for this pallet.".into()) }
			Ok(batches)
		}
	}
}
