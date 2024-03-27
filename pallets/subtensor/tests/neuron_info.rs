mod mock;
use codec::Compact;
use frame_support::assert_ok;
use frame_system::Config;
use mock::*;
use sp_core::U256;

#[test]
fn test_get_neuron_none() {
    new_test_ext().execute_with(|| {
        let netuid: u16 = 1;
        let uid: u16 = 42;

        let neuron = SubtensorModule::get_neuron(netuid, uid);
        assert_eq!(neuron, None);
    });
}

#[test]
#[cfg(not(tarpaulin))]
fn test_get_neuron_some() {
    new_test_ext().execute_with(|| {
        let netuid: u16 = 1;

        let tempo: u16 = 2;
        let modality: u16 = 2;

        let uid: u16 = 0;
        let hotkey0 = U256::from(0);
        let coldkey0 = U256::from(0);

        add_network(netuid, tempo, modality);
        register_ok_neuron(netuid, hotkey0, coldkey0, 39420842);

        let neuron = SubtensorModule::get_neuron(netuid, uid);
        assert_ne!(neuron, None);
    });
}

/* @TODO: Add more neurons to list */
#[test]
fn test_get_neurons_list() {
    new_test_ext().execute_with(|| {
        let netuid: u16 = 1;

        let tempo: u16 = 2;
        let modality: u16 = 2;

        add_network(netuid, tempo, modality);

        let _uid: u16 = 42;

        let neuron_count = 1;
        for index in 0..neuron_count {
            let hotkey = U256::from(0 + index);
            let coldkey = U256::from(0 + index);
            let nonce: u64 = 39420842 + index;
            register_ok_neuron(netuid, hotkey, coldkey, nonce);
        }

        let neurons = SubtensorModule::get_neurons(netuid);
        log::info!("neurons: {:?}", neurons);
        assert_eq!(neurons.len(), neuron_count as usize);
    });
}

#[test]
fn test_get_neurons_empty() {
    new_test_ext().execute_with(|| {
        let netuid: u16 = 1;

        let neuron_count = 0;
        let neurons = SubtensorModule::get_neurons(netuid);
        log::info!("neurons: {:?}", neurons);
        assert_eq!(neurons.len(), neuron_count as usize);
    });
}

#[test]
fn test_get_neuron_subnet_staking_info() {
    new_test_ext().execute_with(|| {
        let netuid: u16 = 1;

        let tempo: u16 = 2;
        let modality: u16 = 2;

        let uid: u16 = 0;
        let hotkey0 = U256::from(1);
        let coldkey0 = U256::from(12);
        let stake_amount: u64 = 1;

        add_network(netuid, tempo, modality);
        register_ok_neuron(netuid, hotkey0, coldkey0, 39420842);
        SubtensorModule::add_balance_to_coldkey_account(&coldkey0, stake_amount);

        assert_ok!(SubtensorModule::add_subnet_stake(
            <<Test as Config>::RuntimeOrigin>::signed(coldkey0),
            hotkey0,
            netuid,
            stake_amount,
        ));

        let neuron = SubtensorModule::get_neuron_lite(netuid, uid);
        log::info!("neuron: {:?}", neuron);
        assert_eq!(
            neuron.unwrap().stake,
            vec![(coldkey0, Compact(stake_amount))]
        );
    });
}

#[test]
fn test_get_neuron_subnet_staking_info_multiple() {
    new_test_ext().execute_with(|| {
        let netuid: u16 = 1;

        let tempo: u16 = 2;
        let modality: u16 = 2;

        add_network(netuid, tempo, modality);

        let stake_amounts: [u64; 5] = [1, 2, 3, 4, 5];
        let mut expected_stakes = Vec::new();

        SubtensorModule::set_max_registrations_per_block(netuid, 10);
        SubtensorModule::set_target_registrations_per_interval(netuid, 10);

        for (index, &stake_amount) in stake_amounts.iter().enumerate() {
            let uid: u16 = index as u16;
            let hotkey = U256::from(index as u64);
            let coldkey = U256::from((index + 10) as u64);

            register_ok_neuron(netuid, hotkey, coldkey, 39420842 + index as u64);
            SubtensorModule::add_balance_to_coldkey_account(&coldkey, stake_amount);

            assert_ok!(SubtensorModule::add_subnet_stake(
                <<Test as Config>::RuntimeOrigin>::signed(coldkey),
                hotkey,
                netuid,
                stake_amount,
            ));

            expected_stakes.push((coldkey, Compact(stake_amount)));
            step_block(1);
        }
        log::info!("expected_stakes: {:?}", expected_stakes);
        // Retrieve and assert for each neuron
        for (index, &(ref coldkey, ref stake)) in expected_stakes.iter().enumerate() {
            let uid: u16 = index as u16;
            let neuron =
                SubtensorModule::get_neuron_lite(netuid, uid).expect("Neuron should exist");

            assert!(
                neuron.stake.contains(&(coldkey.clone(), stake.clone())),
                "Stake for uid {} does not match expected value",
                uid
            );
        }
    });
}

#[test]
fn test_get_neuron_stake_based_on_netuid() {
    new_test_ext().execute_with(|| {
        let netuid_root: u16 = 0; // Root network
        let netuid_sub: u16 = 1; // Subnetwork

        let uid_root: u16 = 0;
        let uid_sub: u16 = 1;

        let hotkey_root = U256::from(0);
        let coldkey_root = U256::from(0);
        let stake_amount_root: u64 = 100;

        let hotkey_sub = U256::from(1);
        let coldkey_sub = U256::from(1);
        let stake_amount_sub: u64 = 200;

        // Setup for root network
        add_network(netuid_root, 2, 2);
        add_network(netuid_sub, 2, 2);
        register_ok_neuron(netuid_sub, hotkey_root, coldkey_root, 39420842);
        SubtensorModule::add_balance_to_coldkey_account(&coldkey_root, stake_amount_root);
        assert_ok!(SubtensorModule::add_stake(
            <<Test as Config>::RuntimeOrigin>::signed(coldkey_root),
            hotkey_root,
            stake_amount_root,
        ));

        step_block(1);

        // Setup for subnetwork
        // add_network(netuid_sub, 2, 2);
        register_ok_neuron(netuid_sub, hotkey_sub, coldkey_sub, 39420843);
        SubtensorModule::add_balance_to_coldkey_account(&coldkey_sub, stake_amount_sub);
        assert_ok!(SubtensorModule::add_subnet_stake(
            <<Test as Config>::RuntimeOrigin>::signed(coldkey_sub),
            hotkey_sub,
            netuid_sub,
            stake_amount_sub,
        ));

        // Test for main network
        let neuron_main = SubtensorModule::get_neuron(netuid_sub, uid_root)
            .expect("Neuron should exist for main network");
        assert_eq!(
            neuron_main.stake.len(),
            1,
            "Main network should have 1 stake entry"
        );
        // assert_eq!(
        //     neuron_main.stake[0].1 .0, stake_amount_root,
        //     "Stake amount for main network does not match"
        // );

        // Test for subnetwork
        let neuron_sub = SubtensorModule::get_neuron(netuid_sub, uid_sub)
            .expect("Neuron should exist for subnetwork");
        assert_eq!(
            neuron_sub.stake.len(),
            1,
            "Subnetwork should have 1 stake entry"
        );
        assert_eq!(
            neuron_sub.stake[0].1 .0, stake_amount_sub,
            "Stake amount for subnetwork does not match"
        );
    });
}
