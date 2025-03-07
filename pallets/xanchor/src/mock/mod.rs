pub mod parachain;
pub mod relay_chain;

use std::ops::Mul;

use frame_support::traits::{GenesisBuild, OnInitialize};
use polkadot_parachain::primitives::Id as ParaId;
use sp_runtime::traits::AccountIdConversion;
use xcm_simulator::{decl_test_network, decl_test_parachain, decl_test_relay_chain};

pub const INITIAL_BALANCE: u128 = 1_000_000_000;
pub const PARAID_A: u32 = 2000;
pub const PARAID_B: u32 = 3000;

decl_test_parachain! {
	pub struct ParaA {
		Runtime = parachain::Runtime,
		XcmpMessageHandler = parachain::MsgQueue,
		DmpMessageHandler = parachain::MsgQueue,
		new_ext = para_ext(PARAID_A),
	}
}

decl_test_parachain! {
	pub struct ParaB {
		Runtime = parachain::Runtime,
		XcmpMessageHandler = parachain::MsgQueue,
		DmpMessageHandler = parachain::MsgQueue,
		new_ext = para_ext(PARAID_B),
	}
}

decl_test_relay_chain! {
	pub struct Relay {
		Runtime = relay_chain::Runtime,
		XcmConfig = relay_chain::XcmConfig,
		new_ext = relay_ext(),
	}
}

decl_test_network! {
	pub struct MockNet {
		relay_chain = Relay,
		parachains = vec![
			(PARAID_A, ParaA),
			(PARAID_B, ParaB),
		],
	}
}

pub fn para_account_id(id: u32) -> relay_chain::AccountId {
	ParaId::from(id).into_account()
}

pub fn para_ext(para_id: u32) -> sp_io::TestExternalities {
	use parachain::{MsgQueue, Runtime};

	let mut t = frame_system::GenesisConfig::default().build_storage::<Runtime>().unwrap();

	pallet_balances::GenesisConfig::<Runtime> {
		balances: vec![
			(parachain::AccountOne::get(), INITIAL_BALANCE.mul(1u128)),
			(parachain::AccountTwo::get(), INITIAL_BALANCE.mul(2u128)),
			(parachain::AccountThree::get(), INITIAL_BALANCE.mul(3u128)),
			(parachain::AccountFour::get(), INITIAL_BALANCE.mul(4u128)),
			(parachain::AccountFive::get(), INITIAL_BALANCE.mul(5u128)),
			(parachain::AccountSix::get(), INITIAL_BALANCE.mul(6u128)),
			(para_account_id(PARAID_A), INITIAL_BALANCE),
			(para_account_id(PARAID_B), INITIAL_BALANCE),
		],
	}
	.assimilate_storage(&mut t)
	.unwrap();
	pallet_democracy::GenesisConfig::<Runtime>::default()
		.assimilate_storage(&mut t)
		.unwrap();
	let mut ext = sp_io::TestExternalities::new(t);
	ext.execute_with(|| {
		next_block();
		MsgQueue::set_para_id(para_id.into());
	});
	ext
}

pub fn relay_ext() -> sp_io::TestExternalities {
	use relay_chain::{Runtime, System};

	let mut t = frame_system::GenesisConfig::default().build_storage::<Runtime>().unwrap();

	pallet_balances::GenesisConfig::<Runtime> {
		balances: vec![
			(parachain::AccountOne::get(), INITIAL_BALANCE),
			(parachain::AccountTwo::get(), INITIAL_BALANCE),
			(parachain::AccountThree::get(), INITIAL_BALANCE),
			(parachain::AccountFour::get(), INITIAL_BALANCE),
			(parachain::AccountFive::get(), INITIAL_BALANCE),
			(parachain::AccountSix::get(), INITIAL_BALANCE),
			(para_account_id(PARAID_A), INITIAL_BALANCE),
			(para_account_id(PARAID_B), INITIAL_BALANCE),
		],
	}
	.assimilate_storage(&mut t)
	.unwrap();

	let mut ext = sp_io::TestExternalities::new(t);
	ext.execute_with(|| System::set_block_number(1));
	ext
}

pub type RelayChainPalletXcm = pallet_xcm::Pallet<relay_chain::Runtime>;
pub type ParachainPalletXcm = pallet_xcm::Pallet<parachain::Runtime>;

pub fn next_block() {
	parachain::System::set_block_number(parachain::System::block_number() + 1);
	parachain::Scheduler::on_initialize(parachain::System::block_number());
	parachain::Democracy::on_initialize(parachain::System::block_number());
}

pub fn fast_forward_to(n: u64) {
	while parachain::System::block_number() < n {
		next_block();
	}
}
