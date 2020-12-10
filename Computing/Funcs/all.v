Definition Participant_Ф_receiveRewardStake ( $ Л_roundId : XInteger32 )( $ Л_reward : XInteger64 )( $ Л_stake : XInteger64 )( $ Л_reinvest : XBool )( $ Л_fee : XInteger64 )( $ Л_reason : XInteger8 ) : ParticipantT True 
 	 := return I .
Definition Participant_Ф_receiveAnswer ( $ Л_errcode : XInteger32 )( $ Л_comment : XInteger64 ) : ParticipantT True 
 	 := return I .
Definition Participant_Ф_receiveRewardStake ( $ Л_roundId : XInteger32 )( $ Л_reward : XInteger64 )( $ Л_stake : XInteger64 )( $ Л_reinvest : XBool )( $ Л_fee : XInteger64 )( $ Л_reason : XInteger8 ) : ParticipantT True 
 	 := return I .
Definition Participant_Ф_receiveAnswer ( $ Л_errcode : XInteger32 )( $ Л_comment : XInteger64 ) : ParticipantT True 
 	 := return I .
Definition StakingProxyContract_Ф_process_new_stake ( msg_value : XInteger ) ( msg_sender : XInteger ) ( $ Л_queryId : XInteger64 )( $ Л_validatorKey : XInteger256 )( $ Л_stakeAt : XInteger32 )( $ Л_maxFactor : XInteger32 )( $ Л_adnlAddr : XInteger256 )( $ Л_signature : XInteger8 ) : StakingProxyContractT := 
 require (( $ msg_sender ?== StakingProxyContract_ι_m_staking , $ xInt102 )) ) >> 
 	 IElector (( ElectorBase_ι_m_elector )) . _Ф_elector_process_new_stake ^^ value (( $ msg_value - StakingProxyContract_ι_PROXY_FEE )) (( $ Л_queryId , $ Л_validatorKey , $ Л_stakeAt , $ Л_maxFactor , $ Л_adnlAddr , $ Л_signature )) ) >> 
 	 
 >> return ; . 
 

Definition StakingProxyContract_Ф_recover_stake ( msg_value : XInteger ) ( msg_sender : XInteger ) ( $ Л_queryId : XInteger64 ) : StakingProxyContractT := 
 require (( $ msg_sender ?== StakingProxyContract_ι_m_staking , $ xInt102 )) ) >> 
 	 IElector (( ElectorBase_ι_m_elector )) . _Ф_elector_recover_stake ^^ value (( $ msg_value - StakingProxyContract_ι_PROXY_FEE )) (( $ Л_queryId )) ) >> 
 	 
 >> return ; . 
 

Definition StakingContract_Ф_receiveConfirmation ( msg_sender : XInteger ) ( $ Л_queryId : XInteger64 )( $ Л_comment : XInteger32 ) : StakingContractT := 
 require (( $ msg_sender ?== ElectorBase_ι_m_elector , $ xInt107 )) ) >> 
 	 require (( $ Л_comment ?== $ xInt0 , $ xInt110 )) ) >> 
 	 require (( $ Л_queryId ?>= $ xInt0 , $ xInt110 )) ) >> 
 	 
 >> return ; . 
 

Definition StakingContract_Ф_receiveReturnedStake ( $ Л_queryId : XInteger64 )( $ Л_comment : XInteger32 ) : StakingContractT XInteger64 # XInteger32 := 
 ( d0! Л_round := RoundsBase_Ф__getPenultimateRound () ) >> 
 	 ( d2! Л_round ^^ RoundsBase_ι_Round_ι_completionStatus := RoundsBase_ι_ROUND_STAKE_REJECTED ) >> 
 	 RoundsBase_Ф__setPenultimateRound (( StakingContract_Ф__completeRound (( RoundsBase_Ф__getPenultimateRound () , StakingContract_ι_MAX_MSGS_PER_TR )) )) ) >> 
 	 return (( $ Л_queryId , $ Л_comment )) ) >> 
 	 
 >> return ; . 
 

Definition StakingContract_Ф_acceptRecoveredStake ( msg_sender : XInteger ) ( $ Л_queryId : XInteger64 ) : StakingContractT := 
 require (( $ msg_sender ?== ElectorBase_ι_m_elector , $ xInt107 )) ) >> 
 	 
 Ife ( $ Л_queryId ?== $ xInt0 ) { StakingContract_Ф__acceptUnusedStake () ) >> 
 	 
 } 
 else 
 Ife ( $ Л_queryId ?== $ xInt1 ) { StakingContract_Ф__acceptRewardStake () ) >> 
 	 
 } 
 else 
 { 
 StakingContract_Ф__acceptPendingRoundStake (( uint32 (( $ Л_queryId )) )) ) >> 
 	 
 } >> 
 
 >> return ; . 
 

Definition StakingContract_Ф_ticktock ( msg_sender : XInteger ) : StakingContractT := 
 require (( $ msg_sender ?!= xInt0 , $ xInt108 )) ) >> 
 	 ( d0! Л_electionsStarted := now ?>= ElectionParams_Ф__getElectionsStart () ) >> 
 	 
 Ife ( $ Л_electionsStarted ) { StakingContract_Ф__addNewRoundAndUpdateRounds () ) >> 
 	 
 } 
 else 
 Ife ( RoundsBase_Ф__getRoundsCount () ?< $ xInt2 ) { 
 Ife ( RoundsBase_Ф__getRoundsCount () ?== $ xInt0 )) StakingContract_Ф__addNewRoundAndUpdateRounds () ) >> 
 	 
 } 
 else 
 Ife ( StakingContract_Ф__checkPenultimateRound () ) { 
 } 
 else 
 Ift ( StakingContract_Ф__checkOldestRound () ) { 
 } >> 
 StakingContract_Ф__returnGrams () ) >> 
 	 
 >> return ; . 
 

Definition Stakeholder_Ф_sendTransaction ( $ Л_dest : XAddress )( $ Л_value : XInteger64 )( $ Л_bounce : XBool )( $ Л_flags : XInteger16 )( $ Л_payload : TvmCell ) : StakeholderT := 
 require (( $ msg_pubkey () ?== tvm_pubkey () , $ xInt100 )) ) >> 
 	 tvm_accept () ) >> 
 	 $ Л_dest ^^ transfer (( $ Л_value , $ Л_bounce , $ Л_flags , $ Л_payload )) ) >> 
 	 
 >> return ; . 
 

Definition AcceptBase_Ф_Constructor1 : AcceptBaseT := 
 require (( $ msg_pubkey () ?== tvm_pubkey () , $ xInt300 )) ) >> 
 	 tvm_accept () ) >> 
 	 
 >> return ; . 
 

Definition OwnerBase_Ф_Constructor2 ( $ Л_poolOwnerAddr : XAddress ) : OwnerBaseT := 
 ( d1! OwnerBase_ι_m_owner := OwnerBase_ι_Owner (( $ Л_poolOwnerAddr , $ xInt0 )) ) >> 
 	 
 >> return ; . 
 

Definition OwnerBase_Ф_withdrawOwnerReward ( msg_sender : XInteger ) ( $ Л_amount : XInteger64 ) : OwnerBaseT := 
 require (( $ msg_sender ?== OwnerBase_ι_Owner_ι_addr , $ xInt106 )) ) >> 
 	 require (( $ Л_amount ?<= OwnerBase_ι_Owner_ι_reward , $ xInt105 )) ) >> 
 	 ( d1! OwnerBase_ι_Owner_ι_reward -= $ Л_amount ) >> 
 	 OwnerBase_ι_Owner_ι_addr . transfer (( $ Л_amount , $ xBoolTrue , $ xInt3 )) ) >> 
 	 
 >> return ; . 
 

Definition OwnerBase_Ф__increaseOwnerReward ( $ Л_ownerReward : XInteger64 ) : OwnerBaseT := 
 ( d1! OwnerBase_ι_Owner_ι_reward += $ Л_ownerReward ) >> 
 	 
 >> return ; . 
 

Definition ElectorBase_Ф_Constructor3 ( $ Л_electorAddr : XAddress ) : ElectorBaseT := 
 ( d1! ElectorBase_ι_m_elector := $ Л_electorAddr ) >> 
 	 
 >> return ; . 
 

Definition ElectionParams_Ф__getFreezingPeriod : ElectionParamsT XInteger32 := 
 return ElectionParams_ι_m_electedFor + ElectionParams_ι_m_heldFor ) >> 
 	 
 >> return ; . 
 

Definition ElectionParams_Ф__getNextElectionId : ElectionParamsT XInteger32 := 
 (( _ , , $ Л_utime_until , _ , , _ , , $ Л_ok )) := tvm_configParam (( $ xInt34 )) ) >> 
 	 
 Ift ( ! $ Л_ok ) { ( d0! Л_offset := (( (( uint32 (( now )) - (( ElectionParams_ι_m_electAt - ElectionParams_ι_m_beginBefore )) )) / ElectionParams_ι_m_electedFor + $ xInt1 )) * ElectionParams_ι_m_electedFor ) >> 
 	 ( d0! Л_utime_until := ElectionParams_ι_m_electAt + $ Л_offset ) >> 
 	 
 } >> 
 return $ Л_utime_until ) >> 
 	 
 >> return ; . 
 

Definition ElectionParams_Ф__getElectionsStart : ElectionParamsT XInteger32 := 
 return ElectionParams_ι_m_electAt - ElectionParams_ι_m_beginBefore ) >> 
 	 
 >> return ; . 
 

Definition ElectionParams_Ф__getElectAt : ElectionParamsT XInteger32 := 
 return ElectionParams_ι_m_electAt ) >> 
 	 
 >> return ; . 
 

Definition ElectionParams_Ф__isElectionOver ( $ Л_currentElectAt : XInteger32 ) : ElectionParamsT XBool := 
 return now ?>= (( $ Л_currentElectAt - ElectionParams_ι_m_endBefore )) ) >> 
 	 
 >> return ; . 
 

Definition StakeholderBase_Ф__haveVesting ( $ Л_stakeholder : ι_Stakeholder ) : StakeholderBaseT XBool := 
 return $ Л_stakeholder ^^ StakeholderBase_ι_Stakeholder_ι_periodPayment ?!= $ xInt0 ) >> 
 	 
 >> return ; . 
 

Definition StakeholderBase_Ф__stakeholderSetVesting ( $ Л_stakeholder : ι_Stakeholder )( $ Л_stake : XInteger64 )( $ Л_withdrawalPeriod : XInteger32 )( $ Л_periodPayment : XInteger64 )( $ Л_vestingOwner : XAddress ) : StakeholderBaseT ι_Stakeholder := 
 ( d2! Л_stakeholder ^^ StakeholderBase_ι_Stakeholder_ι_totalStake += $ Л_stake ) >> 
 	 ( d2! Л_stakeholder ^^ StakeholderBase_ι_Stakeholder_ι_lastPaymentUnixTime := uint64 (( now )) ) >> 
 	 ( d2! Л_stakeholder ^^ StakeholderBase_ι_Stakeholder_ι_withdrawalPeriod := $ Л_withdrawalPeriod ) >> 
 	 ( d2! Л_stakeholder ^^ StakeholderBase_ι_Stakeholder_ι_periodPayment := $ Л_periodPayment ) >> 
 	 ( d2! Л_stakeholder ^^ StakeholderBase_ι_Stakeholder_ι_vestingOwner := $ Л_vestingOwner ) >> 
 	 return $ Л_stakeholder ) >> 
 	 
 >> return ; . 
 

Definition StakeholderBase_Ф__stakeholderExists ( $ Л_addr : XAddress ) : StakeholderBaseT XBool := 
 return exists (( $ Л_addr )) ) >> 
 	 
 >> return ; . 
 

Definition StakeholderBase_Ф__getStakeholder ( $ Л_addr : XAddress ) : StakeholderBaseT ι_Stakeholder := 
 return StakeholderBase_ι_m_stakeholders [ $ Л_addr ] ) >> 
 	 
 >> return ; . 
 

Definition StakeholderBase_Ф__stakeholderFetch ( $ Л_addr : XAddress ) : StakeholderBaseT XBool # ι_Stakeholder := 
 return fetch (( $ Л_addr )) ) >> 
 	 
 >> return ; . 
 

Definition StakeholderBase_Ф__setOrDeleteStakeholder ( $ Л_addr : XAddress )( $ Л_stakeholder : ι_Stakeholder ) : StakeholderBaseT := 
 
 Ift ( $ Л_stakeholder ^^ StakeholderBase_ι_Stakeholder_ι_totalStake ?== $ xInt0 )) delete StakeholderBase_ι_m_stakeholders [ $ Л_addr ] ) >> 
 	 else ( d4! StakeholderBase_ι_m_stakeholders [ Л_addr ] := $ Л_stakeholder ) >> 
 	 
 >> return ; . 
 

Definition StakeholderBase_Ф__stakeholderUpdateStake ( $ Л_addr : XAddress )( $ Л_totalStake : XInteger64 )( $ Л_reinvest : XBool ) : StakeholderBaseT := 
 ( d0! Л_user := StakeholderBase_ι_m_stakeholders [ $ Л_addr ] ) >> 
 	 ( d2! Л_user ^^ StakeholderBase_ι_Stakeholder_ι_reinvest := $ Л_reinvest ) >> 
 	 ( d2! Л_user ^^ StakeholderBase_ι_Stakeholder_ι_totalStake += $ Л_totalStake ) >> 
 	 ( d4! StakeholderBase_ι_m_stakeholders [ Л_addr ] := $ Л_user ) >> 
 	 
 >> return ; . 
 

Definition StakeholderBase_Ф__stakeholderUpdateStake2 ( $ Л_stakeholder : ι_Stakeholder )( $ Л_totalStake : XInteger64 )( $ Л_reinvest : XBool ) : StakeholderBaseT ι_Stakeholder := 
 ( d2! Л_stakeholder ^^ StakeholderBase_ι_Stakeholder_ι_reinvest := $ Л_reinvest ) >> 
 	 ( d2! Л_stakeholder ^^ StakeholderBase_ι_Stakeholder_ι_totalStake += $ Л_totalStake ) >> 
 	 return $ Л_stakeholder ) >> 
 	 
 >> return ; . 
 

Definition StakeholderBase_Ф__stakeholderRemoveStake ( $ Л_addr : XAddress )( $ Л_removedStake : XInteger64 )( $ Л_unusedStake : XInteger64 ) : StakeholderBaseT := 
 ( d0! Л_stakeholder := StakeholderBase_ι_m_stakeholders [ $ Л_addr ] ) >> 
 	 ( d2! Л_stakeholder ^^ StakeholderBase_ι_Stakeholder_ι_totalStake -= $ Л_removedStake ) >> 
 	 ( d2! Л_stakeholder ^^ StakeholderBase_ι_Stakeholder_ι_unusedStake -= $ Л_unusedStake ) >> 
 	 
 Ife ( $ Л_stakeholder ^^ StakeholderBase_ι_Stakeholder_ι_totalStake ?== $ xInt0 ) { delete StakeholderBase_ι_m_stakeholders [ $ Л_addr ] ) >> 
 	 
 } 
 else 
 { 
 ( d4! StakeholderBase_ι_m_stakeholders [ Л_addr ] := $ Л_stakeholder ) >> 
 	 
 } >> 
 
 >> return ; . 
 

Definition StakeholderBase_Ф__stakeholderIncreaseTotalAndUnused ( $ Л_stakeholder : ι_Stakeholder )( $ Л_deltaTotal : XInteger64 )( $ Л_deltaUnused : XInteger64 ) : StakeholderBaseT ι_Stakeholder := 
 ( d2! Л_stakeholder ^^ StakeholderBase_ι_Stakeholder_ι_totalStake += $ Л_deltaTotal ) >> 
 	 ( d2! Л_stakeholder ^^ StakeholderBase_ι_Stakeholder_ι_unusedStake += $ Л_deltaUnused ) >> 
 	 return $ Л_stakeholder ) >> 
 	 
 >> return ; . 
 

Definition StakeholderBase_Ф__stakeholderDecreaseTotalAndUnused ( $ Л_stakeholder : ι_Stakeholder )( $ Л_deltaTotal : XInteger64 )( $ Л_deltaUnused : XInteger64 ) : StakeholderBaseT ι_Stakeholder := 
 ( d2! Л_stakeholder ^^ StakeholderBase_ι_Stakeholder_ι_totalStake -= $ Л_deltaTotal ) >> 
 	 ( d2! Л_stakeholder ^^ StakeholderBase_ι_Stakeholder_ι_unusedStake -= $ Л_deltaUnused ) >> 
 	 return $ Л_stakeholder ) >> 
 	 
 >> return ; . 
 

Definition StakeholderBase_Ф__stakeholderSetReinvest ( $ Л_addr : XAddress )( $ Л_flag : XBool ) : StakeholderBaseT := 
 StakeholderBase_ι_m_stakeholders [ $ Л_addr ( d2! ] ^^ StakeholderBase_ι_Stakeholder_ι_reinvest := $ Л_flag ) >> 
 	 
 >> return ; . 
 

Definition StakeholderBase_Ф__stakeholderSetReinvest2 ( $ Л_stakeholder : ι_Stakeholder )( $ Л_flag : XBool ) : StakeholderBaseT ι_Stakeholder := 
 ( d2! Л_stakeholder ^^ StakeholderBase_ι_Stakeholder_ι_reinvest := $ Л_flag ) >> 
 	 return $ Л_stakeholder ) >> 
 	 
 >> return ; . 
 

Definition StakeholderBase_Ф__stakeholderUpdateGrossReward ( $ Л_stakeholder : ι_Stakeholder )( $ Л_reward : XInteger64 ) : StakeholderBaseT ι_Stakeholder := 
 ( d2! Л_stakeholder ^^ StakeholderBase_ι_Stakeholder_ι_grossReward += $ Л_reward ) >> 
 	 return $ Л_stakeholder ) >> 
 	 
 >> return ; . 
 

Definition StakeholderBase_Ф__stakeholderUpdateTotalStake ( $ Л_stakeholder : ι_Stakeholder )( $ Л_newStake : XInteger64 )( $ Л_oldStake : XInteger64 ) : StakeholderBaseT ι_Stakeholder := 
 
 Ift ( $ Л_newStake ?>= $ Л_oldStake )) ( d2! Л_stakeholder ^^ StakeholderBase_ι_Stakeholder_ι_totalStake += $ Л_newStake - $ Л_oldStake ) >> 
 	 else ( d2! Л_stakeholder ^^ StakeholderBase_ι_Stakeholder_ι_totalStake -= $ Л_oldStake - $ Л_newStake ) >> 
 	 return $ Л_stakeholder ) >> 
 	 
 >> return ; . 
 

Definition StakeholderBase_Ф__stakeholderUpdateUnusedStake ( $ Л_addr : XAddress )( $ Л_add : XInteger64 )( $ Л_remove : XInteger64 ) : StakeholderBaseT := 
 StakeholderBase_ι_m_stakeholders [ $ Л_addr ( d2! ] ^^ StakeholderBase_ι_Stakeholder_ι_unusedStake := (( StakeholderBase_ι_m_stakeholders [ $ Л_addr ] ^^ StakeholderBase_ι_Stakeholder_ι_unusedStake + $ Л_add )) - $ Л_remove ) >> 
 	 
 >> return ; . 
 

Definition StakeholderBase_Ф__stakeholderIncreaseUnusedStake ( $ Л_stakeholder : ι_Stakeholder )( $ Л_delta : XInteger64 ) : StakeholderBaseT ι_Stakeholder := 
 ( d2! Л_stakeholder ^^ StakeholderBase_ι_Stakeholder_ι_unusedStake += $ Л_delta ) >> 
 	 return $ Л_stakeholder ) >> 
 	 
 >> return ; . 
 

Definition StakeholderBase_Ф__stakeholderDecreaseUnusedStake ( $ Л_stakeholder : ι_Stakeholder )( $ Л_delta : XInteger64 ) : StakeholderBaseT ι_Stakeholder := 
 ( d2! Л_stakeholder ^^ StakeholderBase_ι_Stakeholder_ι_unusedStake -= $ Л_delta ) >> 
 	 return $ Л_stakeholder ) >> 
 	 
 >> return ; . 
 

Definition StakeholderBase_Ф__stakeholderResetVesting ( $ Л_stakeholder : ι_Stakeholder ) : StakeholderBaseT ι_Stakeholder := 
 ( d2! Л_stakeholder ^^ StakeholderBase_ι_Stakeholder_ι_lastPaymentUnixTime := $ xInt0 ) >> 
 	 ( d2! Л_stakeholder ^^ StakeholderBase_ι_Stakeholder_ι_withdrawalPeriod := $ xInt0 ) >> 
 	 ( d2! Л_stakeholder ^^ StakeholderBase_ι_Stakeholder_ι_periodPayment := $ xInt0 ) >> 
 	 ( d2! Л_stakeholder ^^ StakeholderBase_ι_Stakeholder_ι_vestingOwner := xInt0 ) >> 
 	 return $ Л_stakeholder ) >> 
 	 
 >> return ; . 
 

Definition StakeholderBase_Ф__stakeholderUpdateLastPaymentTime ( $ Л_stakeholder : ι_Stakeholder )( $ Л_periodQty : XInteger64 ) : StakeholderBaseT ι_Stakeholder := 
 ( d2! Л_stakeholder ^^ StakeholderBase_ι_Stakeholder_ι_lastPaymentUnixTime += $ Л_periodQty * $ Л_stakeholder ^^ StakeholderBase_ι_Stakeholder_ι_withdrawalPeriod ) >> 
 	 return $ Л_stakeholder ) >> 
 	 
 >> return ; . 
 

Definition StakingOwner_Ф_Constructor5 ( $ Л_pool : XAddress ) : StakingOwnerT := 
 require (( $ msg_pubkey () ?== tvm_pubkey () , $ xInt101 )) ) >> 
 	 ( d1! StakingOwner_ι_m_stakingPool := $ Л_pool ) >> 
 	 
 >> return ; . 
 

Definition StakingOwner_Ф_updateStakingPoolAddress ( $ Л_addr : XAddress ) : StakingOwnerT := 
 require (( $ msg_pubkey () ?== tvm_pubkey () , $ xInt101 )) ) >> 
 	 push (( StakingOwner_ι_Address (( StakingOwner_ι_m_stakingPool )) )) ) >> 
 	 ( d1! StakingOwner_ι_m_stakingPool := $ Л_addr ) >> 
 	 
 >> return ; . 
 

Definition StakingOwner_Ф_getStakingPoolAddress : StakingOwnerT XAddress := 
 ( d1! OwnerBase_ι_Owner_ι_addr := StakingOwner_ι_m_stakingPool ) >> 
 	 
 >> return ; . 
 

Definition StakingOwner_Ф_getHistory : StakingOwnerT ι_М_Address := 
 StakingOwner_ι_m_poolHistory ) >> 
 	 
 >> return ; . 
 

Definition StakingOwner_Ф_onCodeUpgrade : StakingOwnerT True 
 	 := return I .
Definition StakingProxyContract_Ф_Constructor6 ( $ Л_staking : XAddress )( $ Л_elector : XAddress ) : StakingProxyContractT := 
 require (( $ msg_pubkey () ?== tvm_pubkey () , $ xInt100 )) ) >> 
 	 tvm_accept () ) >> 
 	 ( d1! StakingProxyContract_ι_m_staking := $ Л_staking ) >> 
 	 ( d1! ElectorBase_ι_m_elector := $ Л_elector ) >> 
 	 
 >> return ; . 
 

Definition RoundsBase_Ф__getRoundsInfo : RoundsBaseT ι_М_RoundInfo := 
 (( $ Л_index , $ Л_round , $ Л_ok )) := min () ) >> 
 	 while (( $ Л_ok ) { infos ^^ push (( RoundsBase_ι_RoundInfo (( $ Л_round ^^ RoundsBase_ι_Round_ι_id , $ Л_round ^^ RoundsBase_ι_Round_ι_start , $ Л_round ^^ RoundsBase_ι_Round_ι_end , $ Л_round ^^ RoundsBase_ι_Round_ι_step , $ Л_round ^^ RoundsBase_ι_Round_ι_completionStatus , $ Л_round ^^ RoundsBase_ι_Round_ι_stake , $ Л_round ^^ RoundsBase_ι_Round_ι_participantQty , $ Л_round ^^ RoundsBase_ι_Round_ι_rewards )) )) ) >> 
 	 (( $ Л_index , $ Л_round , $ Л_ok )) := next (( $ Л_index )) ) >> 
 	 
 } >> 
 
 >> return ; . 
 

Definition RoundsBase_Ф__getPendingRoundsInfo : RoundsBaseT ι_М_RoundInfo := 
 (( $ Л_key , $ Л_round , $ Л_ok )) := min () ) >> 
 	 while (( $ Л_ok ) { infos ^^ push (( RoundsBase_ι_RoundInfo (( $ Л_round ^^ RoundsBase_ι_Round_ι_id , $ Л_round ^^ RoundsBase_ι_Round_ι_start , $ Л_round ^^ RoundsBase_ι_Round_ι_end , $ Л_round ^^ RoundsBase_ι_Round_ι_step , $ Л_round ^^ RoundsBase_ι_Round_ι_completionStatus , $ Л_round ^^ RoundsBase_ι_Round_ι_stake , $ Л_round ^^ RoundsBase_ι_Round_ι_participantQty , $ Л_round ^^ RoundsBase_ι_Round_ι_rewards )) )) ) >> 
 	 (( $ Л_key , $ Л_round , $ Л_ok )) := next (( $ Л_key )) ) >> 
 	 
 } >> 
 
 >> return ; . 
 

Definition RoundsBase_Ф__getLastRoundIdx : RoundsBaseT XInteger64 := 
 return RoundsBase_ι_m_startIdx + RoundsBase_ι_m_roundsCount - $ xInt1 ) >> 
 	 
 >> return ; . 
 

Definition RoundsBase_Ф__addNewPoolingRound ( $ Л_validationStart : XInteger32 )( $ Л_validationPeriod : XInteger32 ) : RoundsBaseT := 
 RoundsBase_ι_m_rounds [ RoundsBase_ι_m_startIdx + RoundsBase_ι_m_roundsCount RoundsBase_ι_Round (( 
 { 
 RoundsBase_ι_Round_ι_id : $ Л_validationStart , RoundsBase_ι_Round_ι_step : RoundsBase_ι_STEP_POOLING , RoundsBase_ι_Round_ι_participantQty : $ xInt0 , RoundsBase_ι_Round_ι_stake : $ xInt0 , RoundsBase_ι_Round_ι_rewards : $ xInt0 , RoundsBase_ι_Round_ι_unused : $ xInt0 , RoundsBase_ι_Round_ι_completionStatus : RoundsBase_ι_ROUND_UNDEFINED , RoundsBase_ι_Round_ι_start : uint32 (( now )) , RoundsBase_ι_Round_ι_end : $ Л_validationStart + $ Л_validationPeriod 
 } >> 
 )) ) >> 
 	 RoundsBase_ι_m_roundsCount ++ ) >> 
 	 
 >> return ; . 
 

Definition RoundsBase_Ф__getRoundsCount : RoundsBaseT XInteger8 := 
 return RoundsBase_ι_m_roundsCount ) >> 
 	 
 >> return ; . 
 

Definition RoundsBase_Ф__removeOldestRound : RoundsBaseT ι_Round := 
 (( _ , $ Л_round )) := delMin () ) >> 
 	 RoundsBase_ι_m_startIdx ++ ) >> 
 	 RoundsBase_ι_m_roundsCount -- ) >> 
 	 return $ Л_round ) >> 
 	 
 >> return ; . 
 

Definition RoundsBase_Ф__getOldestRound : RoundsBaseT ι_Round := 
 return RoundsBase_ι_m_rounds [ RoundsBase_ι_m_startIdx ] ) >> 
 	 
 >> return ; . 
 

Definition RoundsBase_Ф__setOldestRound ( $ Л_round : ι_Round ) : RoundsBaseT := 
 ( d4! RoundsBase_ι_m_rounds [ RoundsBase_ι_m_startIdx ] := $ Л_round ) >> 
 	 
 >> return ; . 
 

Definition RoundsBase_Ф__roundAddStakeAndVesting ( $ Л_round : ι_Round )( $ Л_addr : XAddress )( $ Л_stake : XInteger64 )( $ Л_vestingStake : XInteger64 ) : RoundsBaseT ι_Round := 
 ( d0! Л_totalStake := $ Л_stake + $ Л_vestingStake ) >> 
 	 
 Ift ( $ Л_totalStake ?== $ xInt0 )) return $ Л_round ) >> 
 	 
 Ift ( ! $ Л_round ^^ RoundsBase_ι_Round_ι_stakes . exists (( $ Л_addr )) ) { $ Л_round ^^ RoundsBase_ι_Round_ι_participantQty ++ ) >> 
 	 
 } >> 
 ( d2! Л_round ^^ RoundsBase_ι_Round_ι_stake += $ Л_totalStake ) >> 
 	 ( d0! Л_sv := $ Л_round ^^ RoundsBase_ι_Round_ι_stakes [ $ Л_addr ] ) >> 
 	 ( d2! Л_sv ^^ RoundsBase_ι_StakeValue_ι_simple += $ Л_stake ) >> 
 	 ( d2! Л_sv ^^ RoundsBase_ι_StakeValue_ι_vesting += $ Л_vestingStake ) >> 
 	 ( d3! Л_round ^^ RoundsBase_ι_Round_ι_stakes [ Л_addr ] := $ Л_sv ) >> 
 	 return $ Л_round ) >> 
 	 
 >> return ; . 
 

Definition RoundsBase_Ф__roundMoveStake ( $ Л_round : ι_Round )( $ Л_source : XAddress )( $ Л_destination : XAddress )( $ Л_amount : XInteger64 ) : RoundsBaseT ι_Round # XInteger64 := 
 (( $ Л_exists , $ Л_sourceStake )) := $ Л_round ^^ RoundsBase_ι_Round_ι_stakes . fetch (( $ Л_source )) ) >> 
 	 
 Ife ( ! $ Л_exists )) return (( $ Л_round , $ xInt0 )) ) >> 
 	 
 Ife ( $ Л_sourceStake ^^ RoundsBase_ι_StakeValue_ι_simple ?>= $ Л_amount ) { ( d0! Л_newSourceStake := $ Л_sourceStake ^^ RoundsBase_ι_StakeValue_ι_simple - $ Л_amount ) >> 
 	 ( d0! Л_deltaDestinationStake := $ Л_amount ) >> 
 	 
 } 
 else 
 { 
 ( d0! Л_newSourceStake := $ xInt0 ) >> 
 	 ( d0! Л_deltaDestinationStake := $ Л_sourceStake ^^ RoundsBase_ι_StakeValue_ι_simple ) >> 
 	 
 } >> 
 
 Ife ( $ Л_newSourceStake ?== $ xInt0 && $ Л_round ^^ RoundsBase_ι_Round_ι_stakes [ $ Л_source ] ^^ RoundsBase_ι_StakeValue_ι_vesting ?== $ xInt0 ) { -- $ Л_round ^^ RoundsBase_ι_Round_ι_participantQty ) >> 
 	 delete $ Л_round ^^ RoundsBase_ι_Round_ι_stakes [ $ Л_source ] ) >> 
 	 
 } 
 else 
 { 
 $ Л_round ^^ RoundsBase_ι_Round_ι_stakes [ $ Л_source ( d2! ] ^^ RoundsBase_ι_StakeValue_ι_simple := $ Л_newSourceStake ) >> 
 	 
 } >> 
 
 Ift ( ! $ Л_round ^^ RoundsBase_ι_Round_ι_stakes . exists (( $ Л_destination )) )) $ Л_round ^^ RoundsBase_ι_Round_ι_participantQty ++ ) >> 
 	 $ Л_round ^^ RoundsBase_ι_Round_ι_stakes [ $ Л_destination ( d2! ] ^^ RoundsBase_ι_StakeValue_ι_simple += $ Л_deltaDestinationStake ) >> 
 	 return (( $ Л_round , $ Л_deltaDestinationStake )) ) >> 
 	 
 >> return ; . 
 

Definition RoundsBase_Ф__addPendingRound ( $ Л_round : ι_Round ) : RoundsBaseT := 
 RoundsBase_ι_m_pendingRounds [ $ Л_round ^^ RoundsBase_ι_Round_ι_id $ Л_round ) >> 
 	 
 >> return ; . 
 

Definition RoundsBase_Ф__removePendingRound ( $ Л_pendingId : XInteger32 ) : RoundsBaseT XBool # ι_Round := 
 (( exists , round )) := fetch (( $ Л_pendingId )) ) >> 
 	 
 Ift ( exists ) { delete RoundsBase_ι_m_pendingRounds [ $ Л_pendingId ] ) >> 
 	 
 } >> 
 
 >> return ; . 
 

Definition RoundsBase_Ф__roundFetchPendingRound ( $ Л_pendingId : XInteger32 ) : RoundsBaseT XBool # ι_Round := 
 return fetch (( $ Л_pendingId )) ) >> 
 	 
 >> return ; . 
 

Definition RoundsBase_Ф__setOrDeletePendingRound ( $ Л_round : ι_Round ) : RoundsBaseT := 
 
 Ife ( $ Л_round ^^ RoundsBase_ι_Round_ι_step ?== RoundsBase_ι_STEP_COMPLETED ) { delete RoundsBase_ι_m_pendingRounds [ $ Л_round ^^ RoundsBase_ι_Round_ι_id ] ) >> 
 	 
 } 
 else 
 { 
 RoundsBase_ι_m_pendingRounds [ $ Л_round ^^ RoundsBase_ι_Round_ι_id $ Л_round ) >> 
 	 
 } >> 
 
 >> return ; . 
 

Definition RoundsBase_Ф__deletePendingRound ( $ Л_id : XInteger32 ) : RoundsBaseT := 
 delete RoundsBase_ι_m_pendingRounds [ $ Л_id ] ) >> 
 	 
 >> return ; . 
 

Definition RoundsBase_Ф_getTotalStake ( $ Л_stakes : ι_StakeValue ) : RoundsBaseT XInteger64 := 
 return $ Л_stakes ^^ RoundsBase_ι_StakeValue_ι_simple + $ Л_stakes ^^ RoundsBase_ι_StakeValue_ι_vesting ) >> 
 	 
 >> return ; . 
 

Definition RoundsBase_Ф_arePendingRoundsEmpty : RoundsBaseT XBool := 
 return empty () ) >> 
 	 
 >> return ; . 
 

Definition RoundsBase_Ф__fetchOldestPendingRound : RoundsBaseT XInteger32 # ι_Round # XBool := 
 return min () ) >> 
 	 
 >> return ; . 
 

Definition StakingContract_Ф__returnGrams ( msg_sender : XInteger ) : StakingContractT := 
 $ msg_sender ^^ transfer (( $ xInt0 , $ xBoolTrue , $ xInt64 )) ) >> 
 	 
 >> return ; . 
 

Definition StakingContract_Ф__calcLastRoundInterest ( $ Л_totalStake : XInteger64 )( $ Л_rewards : XInteger64 ) : StakingContractT XInteger64 := 
 return (( $ Л_totalStake ?!= $ xInt0 )) ? uint64 (( (( $ Л_rewards * $ xInt100 * 1e9 )) / $ Л_totalStake ) : $ xInt0 ) >> 
 	 
 >> return ; . 
 

Definition StakingContract_Ф__addRequest ( $ Л_stakeAt : XInteger32 )( $ Л_request : ι_Request ) : StakingContractT := 
 require (( ! exists (( $ Л_stakeAt )) , $ xInt112 )) ) >> 
 	 ( d4! StakingContract_ι_m_requests [ Л_stakeAt ] := $ Л_request ) >> 
 	 
 >> return ; . 
 

Definition StakingContract_Ф__getStakeAndFeeAndUpdateMinStakeIfNeeded ( $ Л_stake : XInteger64 )( $ Л_reward : XInteger64 )( $ Л_roundStake : XInteger64 )( $ Л_roundRewards : XInteger64 ) : StakingContractT XInteger64 # XInteger64 := 
 
 Ife ( StakingContract_ι_NOTIFY_FEE ?< $ Л_stake + $ Л_reward ) { 
 Ift ( $ Л_reward ?!= $ xInt0 && StakingContract_ι_NOTIFY_FEE ?> $ Л_reward ) { ( d1! StakingContract_ι_m_minStake := uint64 (( (( $ Л_roundStake * StakingContract_ι_NOTIFY_FEE )) / $ Л_roundRewards )) ) >> 
 	 
 } >> 
 return (( $ Л_stake + $ Л_reward - StakingContract_ι_NOTIFY_FEE , StakingContract_ι_NOTIFY_FEE )) ) >> 
 	 
 } 
 else 
 { 
 return (( $ xInt0 , $ Л_stake + $ Л_reward )) ) >> 
 	 
 } >> 
 
 >> return ; . 
 

Definition StakingContract_Ф_Constructor7 ( $ Л_electorAddr : XAddress )( $ Л_poolOwnerAddr : XAddress )( $ Л_electionId : XInteger32 )( $ Л_nodeWallet : XAddress )( $ Л_beginBefore : XInteger32 )( $ Л_endBefore : XInteger32 )( $ Л_heldFor : XInteger32 )( $ Л_electedFor : XInteger32 )( $ Л_minStake : XInteger64 )( $ Л_minRoundStake : XInteger64 )( $ Л_maxRoundStake : XInteger64 ) : StakingContractT := 
 ( d1! StakingContract_ι_m_minStake := $ Л_minStake ) >> 
 	 ( d1! StakingContract_ι_m_minRoundStake := $ Л_minRoundStake ) >> 
 	 ( d1! StakingContract_ι_m_maxRoundStake := $ Л_maxRoundStake ) >> 
 	 ( d1! StakingContract_ι_m_poolClosed := $ xBoolFalse ) >> 
 	 ( d1! StakingContract_ι_m_node := StakingContract_ι_Node (( $ Л_nodeWallet , $ xInt3 * $ xInt65536 , $ xInt0 )) ) >> 
 	 
 >> return ; . 
 

Definition StakingContract_Ф_receiveConfirmation ( msg_sender : XInteger ) ( $ Л_queryId : XInteger64 )( $ Л_comment : XInteger32 ) : StakingContractT := 
 require (( $ msg_sender ?== ElectorBase_ι_m_elector , $ xInt107 )) ) >> 
 	 require (( $ Л_comment ?== $ xInt0 , $ xInt110 )) ) >> 
 	 require (( $ Л_queryId ?>= $ xInt0 , $ xInt110 )) ) >> 
 	 
 >> return ; . 
 

Definition DePool_Ф_Constructor8 ( $ Л_electorAddr : XAddress )( $ Л_poolOwnerAddr : XAddress )( $ Л_electionId : XInteger32 )( $ Л_nodeWallet : XAddress )( $ Л_beginBefore : XInteger32 )( $ Л_endBefore : XInteger32 )( $ Л_heldFor : XInteger32 )( $ Л_electedFor : XInteger32 )( $ Л_minStake : XInteger64 )( $ Л_minRoundStake : XInteger64 )( $ Л_maxRoundStake : XInteger64 ) : DePoolT True 
 	 := return I .
Definition DePool_Ф_getOwnerReward : DePoolT XInteger64 := 
 ( d1! OwnerBase_ι_Owner_ι_reward := OwnerBase_ι_Owner_ι_reward ) >> 
 	 
 >> return ; . 
 

Definition DePool_Ф_getMinStake : DePoolT XInteger64 := 
 StakingContract_ι_m_minStake ) >> 
 	 
 >> return ; . 
 

Definition DePool_Ф_getValidator : DePoolT ι_Node := 
 StakingContract_ι_m_node ) >> 
 	 
 >> return ; . 
 

Definition StakingContract_Ф_receiveConfirmation ( msg_sender : XInteger ) ( $ Л_queryId : XInteger64 )( $ Л_comment : XInteger32 ) : StakingContractT := 
 require (( $ msg_sender ?== ElectorBase_ι_m_elector , $ xInt107 )) ) >> 
 	 require (( $ Л_comment ?== $ xInt0 , $ xInt110 )) ) >> 
 	 require (( $ Л_queryId ?>= $ xInt0 , $ xInt110 )) ) >> 
 	 
 >> return ; . 
 

Definition StakingContract_Ф_acceptRecoveredStake ( msg_sender : XInteger ) ( $ Л_queryId : XInteger64 ) : StakingContractT := 
 require (( $ msg_sender ?== ElectorBase_ι_m_elector , $ xInt107 )) ) >> 
 	 
 Ife ( $ Л_queryId ?== $ xInt0 ) { StakingContract_Ф__acceptUnusedStake () ) >> 
 	 
 } 
 else 
 Ife ( $ Л_queryId ?== $ xInt1 ) { StakingContract_Ф__acceptRewardStake () ) >> 
 	 
 } 
 else 
 { 
 StakingContract_Ф__acceptPendingRoundStake (( uint32 (( $ Л_queryId )) )) ) >> 
 	 
 } >> 
 
 >> return ; . 
 

Definition TestElector_Ф_Constructor9 ( $ Л_offset : XInteger32 ) : TestElectorT := 
 ( d1! TestElector_ι_electAt := uint32 (( now )) + $ Л_offset ) >> 
 	 
 >> return ; . 
 

Definition TestElector_Ф_getElectionId : TestElectorT XInteger32 := 
 return TestElector_ι_electAt ) >> 
 	 
 >> return ; . 
 

Definition ElectorBase_Ф__recoverStakes : ElectorBaseT := 
 IProxy (( ElectorBase_ι_m_elector )) . Participant_Ф_recover_stake ^^ value (( ElectorBase_ι_RECOVER_STAKE_MSG_VALUE )) (( $ xInt0 )) ) >> 
 	 
 >> return ; . 
 

Definition ElectorBase_Ф__recoverStakeRewards : ElectorBaseT := 
 IProxy (( ElectorBase_ι_m_elector )) . Participant_Ф_recover_stake ^^ value (( ElectorBase_ι_RECOVER_STAKE_MSG_VALUE )) (( $ xInt1 )) ) >> 
 	 
 >> return ; . 
 

Definition ElectorBase_Ф__recoverPendingRoundStakes ( $ Л_pendingId : XInteger32 ) : ElectorBaseT := 
 IProxy (( ElectorBase_ι_m_elector )) . Participant_Ф_recover_stake ^^ value (( ElectorBase_ι_RECOVER_STAKE_MSG_VALUE )) (( $ Л_pendingId )) ) >> 
 	 
 >> return ; . 
 

Definition ElectorBase_Ф__runForElection ( $ Л_req : ι_Request )( $ Л_nodeStake : XInteger64 ) : ElectorBaseT := 
 IProxy (( ElectorBase_ι_m_elector )) . Participant_Ф_process_new_stake ^^ value (( $ Л_nodeStake + 1e9 + 2*1e7 )) (( $ Л_req ^^ ElectorBase_ι_Request_ι_queryId , $ Л_req ^^ ElectorBase_ι_Request_ι_validatorKey , $ Л_req ^^ ElectorBase_ι_Request_ι_stakeAt , $ Л_req ^^ ElectorBase_ι_Request_ι_maxFactor , $ Л_req ^^ ElectorBase_ι_Request_ι_adnlAddr , $ Л_req ^^ ElectorBase_ι_Request_ι_signature )) ) >> 
 	 
 >> return ; . 
 

Definition ElectionParams_Ф__getStakingPeriod : ElectionParamsT XInteger32 := 
 return ElectionParams_ι_m_electedFor + ElectionParams_ι_m_beginBefore + ElectionParams_Ф__getFreezingPeriod () ) >> 
 	 
 >> return ; . 
 

Definition ElectionParams_Ф__isRoundUnfrozen ( $ Л_electAt : XInteger32 ) : ElectionParamsT XBool := 
 return now ?> (( $ Л_electAt + ElectionParams_Ф__getFreezingPeriod () )) ) >> 
 	 
 >> return ; . 
 

Definition ElectionParams_Ф__setAndGetNextElectAt : ElectionParamsT XInteger32 := 
 ( d0! Л_nextElectAt := ElectionParams_Ф__getNextElectionId () ) >> 
 	 
 Ift ( now ?>= $ Л_nextElectAt - ElectionParams_ι_m_beginBefore ) { ( d0! Л_nextElectAt += ElectionParams_ι_m_electedFor ) >> 
 	 
 } >> 
 ( d1! ElectionParams_ι_m_electAt := $ Л_nextElectAt ) >> 
 	 return $ Л_nextElectAt ) >> 
 	 
 >> return ; . 
 

Definition StakingOwner_Ф__settimer ( $ Л_timer : XAddress )( $ Л_period : XInteger ) : StakingOwnerT := 
 ITimer (( $ Л_timer )) . StakeholderBase_Ф_setTimer ^^ value (( StakingOwner_ι_TIMER_FEE )) (( $ Л_period )) ) >> 
 	 
 >> return ; . 
 

Definition StakingOwner_Ф_onTimer ( msg_sender : XInteger ) : StakingOwnerT := 
 ( d0! Л_timer := StakingOwner_ι_m_timer ) >> 
 	 ( d0! Л_period := StakingOwner_ι_m_timeout ) >> 
 	 
 Ift ( $ msg_sender ?== $ Л_timer && $ Л_period ?> $ xInt0 ) { IStaking (( StakingOwner_ι_m_stakingPool )) . Participant_Ф_ticktock ^^ value (( StakingOwner_ι_TICKTOCK_FEE )) () ) >> 
 	 StakingOwner_Ф__settimer (( $ Л_timer , $ Л_period )) ) >> 
 	 
 } >> 
 
 >> return ; . 
 

Definition StakingProxyContract_Ф_process_new_stake ( msg_value : XInteger ) ( msg_sender : XInteger ) ( $ Л_queryId : XInteger64 )( $ Л_validatorKey : XInteger256 )( $ Л_stakeAt : XInteger32 )( $ Л_maxFactor : XInteger32 )( $ Л_adnlAddr : XInteger256 )( $ Л_signature : XInteger8 ) : StakingProxyContractT := 
 require (( $ msg_sender ?== StakingProxyContract_ι_m_staking , $ xInt102 )) ) >> 
 	 IElector (( ElectorBase_ι_m_elector )) . _Ф_elector_process_new_stake ^^ value (( $ msg_value - StakingProxyContract_ι_PROXY_FEE )) (( $ Л_queryId , $ Л_validatorKey , $ Л_stakeAt , $ Л_maxFactor , $ Л_adnlAddr , $ Л_signature )) ) >> 
 	 
 >> return ; . 
 

Definition StakingProxyContract_Ф_recover_stake ( msg_value : XInteger ) ( msg_sender : XInteger ) ( $ Л_queryId : XInteger64 ) : StakingProxyContractT := 
 require (( $ msg_sender ?== StakingProxyContract_ι_m_staking , $ xInt102 )) ) >> 
 	 IElector (( ElectorBase_ι_m_elector )) . _Ф_elector_recover_stake ^^ value (( $ msg_value - StakingProxyContract_ι_PROXY_FEE )) (( $ Л_queryId )) ) >> 
 	 
 >> return ; . 
 

Definition StakingProxyContract_Ф_receive_confirmation ( msg_value : XInteger ) ( msg_sender : XInteger ) ( $ Л_queryId : XInteger64 )( $ Л_comment : XInteger32 ) : StakingProxyContractT := 
 require (( $ msg_sender ?== ElectorBase_ι_m_elector , $ xInt107 )) ) >> 
 	 IStaking (( StakingProxyContract_ι_m_staking )) . Participant_Ф_receiveConfirmation ^^ value (( $ msg_value - StakingProxyContract_ι_PROXY_FEE )) (( $ Л_queryId , $ Л_comment )) ) >> 
 	 
 >> return ; . 
 

Definition StakingProxyContract_Ф_receive_returned_stake ( msg_value : XInteger ) ( msg_sender : XInteger ) ( $ Л_queryId : XInteger64 )( $ Л_comment : XInteger32 ) : StakingProxyContractT := 
 require (( $ msg_sender ?== ElectorBase_ι_m_elector , $ xInt107 )) ) >> 
 	 IStaking (( StakingProxyContract_ι_m_staking )) . Participant_Ф_receiveReturnedStake ^^ value (( $ msg_value - StakingProxyContract_ι_PROXY_FEE )) (( $ Л_queryId , $ Л_comment )) ) >> 
 	 
 >> return ; . 
 

Definition StakingProxyContract_Ф_accept_recovered_stake ( msg_value : XInteger ) ( msg_sender : XInteger ) ( $ Л_queryId : XInteger64 ) : StakingProxyContractT := 
 require (( $ msg_sender ?== ElectorBase_ι_m_elector , $ xInt107 )) ) >> 
 	 IStaking (( StakingProxyContract_ι_m_staking )) . Participant_Ф_acceptRecoveredStake ^^ value (( $ msg_value - StakingProxyContract_ι_PROXY_FEE )) (( $ Л_queryId )) ) >> 
 	 
 >> return ; . 
 

Definition RoundsBase_Ф__getLastRound : RoundsBaseT ι_Round := 
 (( $ Л_exists , $ Л_round )) := fetch (( RoundsBase_Ф__getLastRoundIdx () )) ) >> 
 	 require (( $ Л_exists , $ xInt200 )) ) >> 
 	 return $ Л_round ) >> 
 	 
 >> return ; . 
 

Definition RoundsBase_Ф__setLastRound ( $ Л_round : ι_Round ) : RoundsBaseT := 
 RoundsBase_ι_m_rounds [ RoundsBase_Ф__getLastRoundIdx () $ Л_round ) >> 
 	 
 >> return ; . 
 

Definition RoundsBase_Ф__getPenultimateRound : RoundsBaseT ι_Round := 
 return RoundsBase_ι_m_rounds [ RoundsBase_Ф__getLastRoundIdx () - $ xInt1 ] ) >> 
 	 
 >> return ; . 
 

Definition RoundsBase_Ф__setPenultimateRound ( $ Л_round : ι_Round ) : RoundsBaseT := 
 RoundsBase_ι_m_rounds [ RoundsBase_Ф__getLastRoundIdx () - $ xInt1 $ Л_round ) >> 
 	 
 >> return ; . 
 

Definition StakingContract_Ф__addNewRoundAndUpdateRounds : StakingContractT := 
 RoundsBase_Ф__addNewPoolingRound (( ElectionParams_Ф__setAndGetNextElectAt () , ElectionParams_Ф__getFreezingPeriod () )) ) >> 
 	 
 Ift ( RoundsBase_Ф__getRoundsCount () ?> $ xInt4 ) { ( d0! Л_removingRound := RoundsBase_Ф__removeOldestRound () ) >> 
 	 delete StakingContract_ι_m_requests [ $ Л_removingRound ^^ RoundsBase_ι_Round_ι_id ] ) >> 
 	 
 Ift ( $ Л_removingRound ^^ RoundsBase_ι_Round_ι_step ?== RoundsBase_ι_STEP_WAITING_ELECTION_RESULTS ) { RoundsBase_Ф__addPendingRound (( $ Л_removingRound )) ) >> 
 	 ElectorBase_Ф__recoverPendingRoundStakes (( $ Л_removingRound ^^ RoundsBase_ι_Round_ι_id )) ) >> 
 	 
 } >> 
 
 } >> 
 
 Ift ( RoundsBase_Ф__getRoundsCount () ?> $ xInt1 ) { RoundsBase_Ф__setPenultimateRound (( StakingContract_Ф__requestStakesSigning (( RoundsBase_Ф__getPenultimateRound () )) )) ) >> 
 	 
 } >> 
 
 >> return ; . 
 

Definition StakingContract_Ф__checkPenultimateRound : StakingContractT XBool := 
 ( d0! Л_lb1Round := RoundsBase_Ф__getPenultimateRound () ) >> 
 	 
 Ift ( now ?> $ Л_lb1Round ^^ RoundsBase_ι_Round_ι_id ) { 
 Ift ( $ Л_lb1Round ^^ RoundsBase_ι_Round_ι_step ?< RoundsBase_ι_STEP_ELECTIONS ) { RoundsBase_Ф__setPenultimateRound (( StakingContract_Ф__completeRoundAndSetCompletionStatus (( $ Л_lb1Round , RoundsBase_ι_ROUND_MISSED_ELECTIONS )) )) ) >> 
 	 return $ xBoolTrue ) >> 
 	 
 } >> 
 
 Ift ( $ Л_lb1Round ^^ RoundsBase_ι_Round_ι_step ?< RoundsBase_ι_STEP_WAITING_ELECTION_RESULTS ) { ElectorBase_Ф__recoverStakes () ) >> 
 	 ( d2! Л_lb1Round ^^ RoundsBase_ι_Round_ι_step := RoundsBase_ι_STEP_WAITING_ELECTION_RESULTS ) >> 
 	 RoundsBase_Ф__setPenultimateRound (( $ Л_lb1Round )) ) >> 
 	 return $ xBoolTrue ) >> 
 	 
 } >> 
 
 } >> 
 return $ xBoolFalse ) >> 
 	 
 >> return ; . 
 

Definition StakingContract_Ф__checkOldestRound : StakingContractT XBool := 
 ( d0! Л_oldestRound := RoundsBase_Ф__getOldestRound () ) >> 
 	 
 Ift ( ElectionParams_Ф__isRoundUnfrozen (( $ Л_oldestRound ^^ RoundsBase_ι_Round_ι_id )) ) { 
 Ift ( $ Л_oldestRound ^^ RoundsBase_ι_Round_ι_step ?== RoundsBase_ι_STEP_WAITING_ELECTION_RESULTS ) { ElectorBase_Ф__recoverStakeRewards () ) >> 
 	 ( d2! Л_oldestRound ^^ RoundsBase_ι_Round_ι_step := RoundsBase_ι_STEP_WAITING_UNFREEZE ) >> 
 	 RoundsBase_Ф__setOldestRound (( $ Л_oldestRound )) ) >> 
 	 return $ xBoolTrue ) >> 
 	 
 } >> 
 
 } >> 
 return $ xBoolFalse ) >> 
 	 
 >> return ; . 
 

Definition StakingContract_Ф__returnAnswer ( msg_sender : XInteger ) ( $ Л_errcode : XInteger32 )( $ Л_amount : XInteger64 )( $ Л_comment : XInteger64 ) : StakingContractT := 
 IParticipant (( $ msg_sender )) . _Ф_receiveAnswer 
 { 
 value : $ Л_amount , flag : (( $ Л_amount ?== $ xInt0 ? $ xInt64 : $ xInt3 )) 
 } >> 
 (( $ Л_errcode , $ Л_comment )) ) >> 
 	 
 >> return ; . 
 

Definition StakingContract_Ф__returnError ( $ Л_errcode : XInteger32 )( $ Л_comment : XInteger64 ) : StakingContractT := 
 StakingContract_Ф__returnAnswer (( $ Л_errcode , $ xInt0 , $ Л_comment )) ) >> 
 	 
 >> return ; . 
 

Definition StakingContract_Ф__returnConfirmation ( $ Л_fee : XInteger64 ) : StakingContractT := 
 StakingContract_Ф__returnAnswer (( StakingContract_ι_STATUS_SUCCESS , StakingContract_ι_ANSWER_MSG_FEE , $ Л_fee )) ) >> 
 	 
 >> return ; . 
 

Definition StakingContract_Ф__investStake ( $ Л_addr : XAddress )( $ Л_unusedStake : XInteger64 )( $ Л_newStake : XInteger64 )( $ Л_reinvest : XBool ) : StakingContractT XBool := 
 ( d0! Л_stakeholder := StakeholderBase_Ф__getStakeholder (( $ Л_addr )) ) >> 
 	 ( d0! Л_unusedStake := tvm_min (( $ Л_unusedStake , $ Л_stakeholder ^^ StakeholderBase_ι_Stakeholder_ι_unusedStake )) ) >> 
 	 ( d0! Л_investStake := $ Л_unusedStake + $ Л_newStake ) >> 
 	 ( d0! Л_round := RoundsBase_Ф__getLastRound () ) >> 
 	 
 Ift ( $ Л_round ^^ RoundsBase_ι_Round_ι_stake + $ Л_investStake ?> StakingContract_ι_m_maxRoundStake ) { return $ xBoolFalse ) >> 
 	 
 } >> 
 RoundsBase_Ф__setLastRound (( RoundsBase_Ф__roundAddStakeAndVesting (( $ Л_round , $ Л_addr , $ Л_investStake , $ xInt0 )) )) ) >> 
 	 $ Л_stakeholder $ Л_=_stakeholderDecreaseUnusedStake (( $ Л_stakeholder , $ Л_unusedStake )) ) >> 
 	 
 Ife ( $ Л_newStake ?> $ xInt0 ) { ( d0! Л_stakeholder := StakeholderBase_Ф__stakeholderUpdateStake2 (( $ Л_stakeholder , $ Л_newStake , $ Л_reinvest )) ) >> 
 	 
 } 
 else 
 { 
 ( d0! Л_stakeholder := StakeholderBase_Ф__stakeholderSetReinvest2 (( $ Л_stakeholder , $ Л_reinvest )) ) >> 
 	 
 } >> 
 StakeholderBase_Ф__setOrDeleteStakeholder (( $ Л_addr , $ Л_stakeholder )) ) >> 
 	 return $ xBoolTrue ) >> 
 	 
 >> return ; . 
 

Definition StakingContract_Ф__requestStakesSigning ( $ Л_round : ι_Round ) : StakingContractT ι_Round := 
 ( d0! Л_roundStake := $ Л_round ^^ RoundsBase_ι_Round_ι_stake ) >> 
 	 ( d0! Л_currentElectAt := $ Л_round ^^ RoundsBase_ι_Round_ι_id ) >> 
 	 ( d0! Л_roundStakeCheck := $ Л_roundStake ?>= StakingContract_ι_m_minRoundStake ) >> 
 	 ( d0! Л_nodeStakeCheck := RoundsBase_Ф_getTotalStake (( $ Л_round ^^ RoundsBase_ι_Round_ι_stakes [ StakingContract_ι_Node_ι_wallet ] )) ?>= (( StakingContract_ι_m_minRoundStake * StakingContract_ι_NODE_WALLET_MIN_STAKE )) / $ xInt100 ) >> 
 	 ( d0! Л_canParticipate := ! ElectionParams_Ф__isElectionOver (( $ Л_currentElectAt )) && $ Л_roundStakeCheck && $ Л_nodeStakeCheck ) >> 
 	 
 Ife ( $ Л_canParticipate ) { ( d1! RoundsBase_ι_Round_ι_stake := $ Л_roundStake ) >> 
 	 emit $ Л_stakeSigningRequested (( $ Л_currentElectAt )) ) >> 
 	 (( $ Л_exists , $ Л_request )) := fetch (( $ Л_currentElectAt )) ) >> 
 	 
 Ife ( $ Л_exists ) { ( d2! Л_round ^^ RoundsBase_ι_Round_ι_step := RoundsBase_ι_STEP_ELECTIONS ) >> 
 	 ElectorBase_Ф__runForElection (( $ Л_request , $ Л_roundStake )) ) >> 
 	 
 } 
 else 
 { 
 ( d2! Л_round ^^ RoundsBase_ι_Round_ι_step := RoundsBase_ι_STEP_WAITING_REQUESTS ) >> 
 	 
 } >> 
 
 } 
 else 
 { 
 ( d0! Л_completionStatus := ! $ Л_roundStakeCheck ? RoundsBase_ι_ROUND_NOT_ENOUGH_TOTAL_STAKE : RoundsBase_ι_ROUND_NODE_STAKE_TOO_SMALL ) >> 
 	 ( d0! Л_round := StakingContract_Ф__completeRoundAndSetCompletionStatus (( $ Л_round , $ Л_completionStatus )) ) >> 
 	 
 } >> 
 return $ Л_round ) >> 
 	 
 >> return ; . 
 

Definition StakingContract_Ф__acceptPendingRoundStake ( $ Л_pendingId : XInteger32 ) : StakingContractT := 
 (( $ Л_exists , $ Л_round )) := RoundsBase_Ф__removePendingRound (( $ Л_pendingId )) ) >> 
 	 
 Ift ( $ Л_exists ) { StakingContract_Ф__completeRoundAndSetCompletionStatus (( $ Л_round , RoundsBase_ι_ROUND_RECEIVED_REWARD )) ) >> 
 	 
 } >> 
 
 >> return ; . 
 

Definition StakingContract_Ф__acceptUnusedStake ( msg_value : XInteger ) : StakingContractT := 
 ( d0! Л_lb1round := RoundsBase_Ф__getPenultimateRound () ) >> 
 	 
 Ife ( $ msg_value ?>= $ Л_lb1round ^^ RoundsBase_ι_Round_ι_stake ) { RoundsBase_Ф__setPenultimateRound (( StakingContract_Ф__completeRoundAndSetCompletionStatus (( $ Л_lb1round , RoundsBase_ι_ROUND_LOST_ELECTIONS )) )) ) >> 
 	 ( d1! StakingContract_ι_m_minRoundStake += StakingContract_ι_m_minRoundStake / $ xInt4 ) >> 
 	 
 } 
 else 
 { 
 ( d2! Л_lb1round ^^ RoundsBase_ι_Round_ι_unused := uint64 (( $ msg_value )) ) >> 
 	 ( d1! StakingContract_ι_m_minRoundStake := $ Л_lb1round ^^ RoundsBase_ι_Round_ι_stake - $ Л_lb1round ^^ RoundsBase_ι_Round_ι_unused + StakingContract_ι_ROUND_UP_VALUE ) >> 
 	 
 } >> 
 
 >> return ; . 
 

Definition StakingContract_Ф__acceptRewardStake ( msg_value : XInteger ) : StakingContractT := 
 ( d0! Л_oldestRound := RoundsBase_Ф__getOldestRound () ) >> 
 	 ( d0! Л_roundStake := $ Л_oldestRound ^^ RoundsBase_ι_Round_ι_stake - $ Л_oldestRound ^^ RoundsBase_ι_Round_ι_unused ) >> 
 	 ( d0! Л_totalReward := $ xInt0 ) >> 
 	 
 Ift ( uint64 (( $ msg_value )) ?>= $ Л_roundStake ) { ( d0! Л_totalReward := uint64 (( $ msg_value )) - $ Л_roundStake ) >> 
 	 
 } >> 
 ( d0! Л_roundReward := uint64 (( (( $ Л_totalReward * StakingContract_ι_NOM_FRACTION )) / $ xInt100 )) ) >> 
 	 ( d0! Л_ownerReward := uint64 (( (( $ Л_totalReward * StakingContract_ι_NODE_FRACTION )) / $ xInt100 )) ) >> 
 	 OwnerBase_Ф__increaseOwnerReward (( $ Л_ownerReward )) ) >> 
 	 ( d2! Л_oldestRound ^^ RoundsBase_ι_Round_ι_rewards := $ Л_roundReward ) >> 
 	 ( d1! StakingContract_ι_m_lastRoundInterest := StakingContract_Ф__calcLastRoundInterest (( $ Л_roundStake , $ Л_roundReward )) ) >> 
 	 RoundsBase_Ф__setOldestRound (( StakingContract_Ф__completeRoundAndSetCompletionStatus (( $ Л_oldestRound , RoundsBase_ι_ROUND_RECEIVED_REWARD )) )) ) >> 
 	 
 >> return ; . 
 

Definition StakingContract_Ф__completeRound ( $ Л_completedRound : ι_Round )( $ Л_chunkSize : XInteger8 ) : StakingContractT ι_Round := 
 ( d2! Л_completedRound ^^ RoundsBase_ι_Round_ι_step := RoundsBase_ι_STEP_COMPLETING ) >> 
 	 ( d2! Л_completedRound ^^ RoundsBase_ι_Round_ι_end := uint32 (( now )) ) >> 
 	 RoundsBase_Ф__setOrDeletePendingRound (( $ Л_completedRound )) ) >> 
 	 tvm_accept () ) >> 
 	 tvm_commit () ) >> 
 	 ( d0! Л_completedRound := StakingContract_Ф__completePendingRound (( $ Л_completedRound , $ Л_chunkSize )) ) >> 
 	 RoundsBase_Ф__setOrDeletePendingRound (( $ Л_completedRound )) ) >> 
 	 delete $ Л_completedRound ^^ RoundsBase_ι_Round_ι_stakes ) >> 
 	 return $ Л_completedRound ) >> 
 	 
 >> return ; . 
 

Definition StakingContract_Ф__completeRoundAndSetCompletionStatus ( $ Л_round : ι_Round )( $ Л_completionStatus : XInteger8 ) : StakingContractT ι_Round := 
 ( d2! Л_round ^^ RoundsBase_ι_Round_ι_completionStatus := $ Л_completionStatus ) >> 
 	 return StakingContract_Ф__completeRound (( $ Л_round , StakingContract_ι_MAX_MSGS_PER_TR )) ) >> 
 	 
 >> return ; . 
 

Definition StakingContract_Ф_getNewStakeAndFees ( $ Л_roundRewards : XInteger64 )( $ Л_roundStake : XInteger64 )( $ Л_stake : XInteger64 ) : StakingContractT XInteger64 # XInteger64 # XInteger64 := 
 
 Ift ( $ Л_stake ?== $ xInt0 ) { return (( $ xInt0 , $ xInt0 , $ xInt0 )) ) >> 
 	 
 } >> 
 ( d0! Л_reward := (( $ Л_roundStake ?!= $ xInt0 )) ? uint64 (( $ Л_roundRewards * $ Л_stake / $ Л_roundStake ) : $ xInt0 ) >> 
 	 (( $ Л_stakeAndReward , $ Л_fee )) := StakingContract_Ф__getStakeAndFeeAndUpdateMinStakeIfNeeded (( $ Л_stake , $ Л_reward , $ Л_roundStake , $ Л_roundRewards )) ) >> 
 	 return (( $ Л_reward , $ Л_stakeAndReward , $ Л_fee )) ) >> 
 	 
 >> return ; . 
 

Definition StakingContract_Ф__returnOrReinvestForStakeholder ( $ Л_completedRound : ι_Round )( $ Л_lastRound : ι_Round )( $ Л_addr : XAddress )( $ Л_stake : ι_StakeValue ) : StakingContractT ι_Round := 
 ( d0! Л_roundRewards := $ Л_completedRound ^^ RoundsBase_ι_Round_ι_rewards ) >> 
 	 ( d0! Л_roundStake := $ Л_completedRound ^^ RoundsBase_ι_Round_ι_stake ) >> 
 	 ( d0! Л_stakeholder := StakeholderBase_Ф__getStakeholder (( $ Л_addr )) ) >> 
 	 ( d0! Л_reinvest := $ Л_stakeholder ^^ StakeholderBase_ι_Stakeholder_ι_reinvest ) >> 
 	 (( $ Л_stakeReward , $ Л_newStake , $ Л_stakeFee )) := StakingContract_Ф_getNewStakeAndFees (( $ Л_roundRewards , $ Л_roundStake , $ Л_stake ^^ RoundsBase_ι_StakeValue_ι_simple )) ) >> 
 	 (( $ Л_vestingReward , $ Л_vestingAndReward , $ Л_vestingFee )) := StakingContract_Ф_getNewStakeAndFees (( $ Л_roundRewards , $ Л_roundStake , $ Л_stake ^^ RoundsBase_ι_StakeValue_ι_vesting )) ) >> 
 	 ( d0! Л_pureVestingReward := $ Л_vestingAndReward ?>= $ Л_stake ^^ vesting? $ Л_vestingAndReward - $ Л_stake ^^ RoundsBase_ι_StakeValue_ι_vesting : $ xInt0 ) >> 
 	 ( d0! Л_newVesting := tvm_min (( $ Л_vestingAndReward - $ Л_pureVestingReward , $ Л_stake ^^ RoundsBase_ι_StakeValue_ι_vesting )) ) >> 
 	 ( d0! Л_stakeholder := StakeholderBase_Ф__stakeholderUpdateGrossReward (( $ Л_stakeholder , $ Л_stakeReward + $ Л_vestingReward )) ) >> 
 	 ( d0! Л_stakeholder := StakeholderBase_Ф__stakeholderUpdateTotalStake (( $ Л_stakeholder , $ Л_newStake + $ Л_vestingAndReward , $ Л_stake ^^ RoundsBase_ι_StakeValue_ι_simple + $ Л_stake ^^ RoundsBase_ι_StakeValue_ι_vesting )) ) >> 
 	 ( d0! Л_withdrawalVesting := $ xInt0 ) >> 
 	 
 Ift ( $ Л_stake ^^ RoundsBase_ι_StakeValue_ι_vesting ?!= $ xInt0 ) { ( d0! Л_periodQty := (( uint64 (( now )) - $ Л_stakeholder ^^ StakeholderBase_ι_Stakeholder_ι_lastPaymentUnixTime )) / $ Л_stakeholder ^^ StakeholderBase_ι_Stakeholder_ι_withdrawalPeriod ) >> 
 	 ( d0! Л_withdrawalVesting := tvm_min (( $ Л_periodQty * $ Л_stakeholder ^^ StakeholderBase_ι_Stakeholder_ι_periodPayment , $ Л_newVesting )) ) >> 
 	 ( d0! Л_newVesting -= $ Л_withdrawalVesting ) >> 
 	 ( d0! Л_stakeholder := StakeholderBase_Ф__stakeholderUpdateLastPaymentTime (( $ Л_stakeholder , $ Л_periodQty )) ) >> 
 	 
 Ift ( $ Л_newVesting ?< StakingContract_ι_m_minStake ) { ( d0! Л_stakeholder := StakeholderBase_Ф__stakeholderIncreaseUnusedStake (( $ Л_stakeholder , $ Л_newVesting )) ) >> 
 	 ( d0! Л_stakeholder := StakeholderBase_Ф__stakeholderResetVesting (( $ Л_stakeholder )) ) >> 
 	 ( d0! Л_newVesting := $ xInt0 ) >> 
 	 
 } >> 
 
 } >> 
 ( d0! Л_newStake += $ Л_withdrawalVesting + $ Л_pureVestingReward ) >> 
 	 
 Ife ( StakingContract_ι_m_poolClosed ) { ( d0! Л_attachedValue := $ Л_newStake + $ Л_stakeholder ^^ StakeholderBase_ι_Stakeholder_ι_unusedStake ) >> 
 	 ( d0! Л_stakeholder := StakeholderBase_Ф__stakeholderDecreaseTotalAndUnused (( $ Л_stakeholder , $ Л_newStake + $ Л_newVesting + $ Л_stakeholder ^^ StakeholderBase_ι_Stakeholder_ι_unusedStake , $ Л_stakeholder ^^ StakeholderBase_ι_Stakeholder_ι_unusedStake )) ) >> 
 	 
 Ift ( $ Л_newVesting ?!= $ xInt0 && $ Л_stakeholder ^^ StakeholderBase_ι_Stakeholder_ι_vestingOwner ?!= xInt0 ) { $ Л_stakeholder ^^ StakeholderBase_ι_Stakeholder_ι_vestingOwner . transfer (( 
 { 
 value : $ Л_newVesting , flag : $ xInt3 
 } >> 
 )) ) >> 
 	 
 } >> 
 ( d0! Л_stakeholder := StakeholderBase_Ф__stakeholderResetVesting (( $ Л_stakeholder )) ) >> 
 	 
 } 
 else 
 { 
 ( d0! Л_attachedValue := $ xInt1 ) >> 
 	 
 Ife ( $ Л_reinvest ) { ( d0! Л_lastRound := RoundsBase_Ф__roundAddStakeAndVesting (( $ Л_lastRound , $ Л_addr , $ Л_newStake , $ Л_newVesting )) ) >> 
 	 
 } 
 else 
 { 
 ( d0! Л_stakeholder := StakeholderBase_Ф__stakeholderIncreaseUnusedStake (( $ Л_stakeholder , $ Л_newStake )) ) >> 
 	 ( d0! Л_lastRound := RoundsBase_Ф__roundAddStakeAndVesting (( $ Л_lastRound , $ Л_addr , $ xInt0 , $ Л_newVesting )) ) >> 
 	 
 } >> 
 
 } >> 
 StakeholderBase_Ф__setOrDeleteStakeholder (( $ Л_addr , $ Л_stakeholder )) ) >> 
 	 IParticipant (( $ Л_addr )) . _Ф_receiveRewardStake 
 { 
 value : $ Л_attachedValue , flag : $ xInt3 
 } >> 
 (( $ Л_completedRound ^^ RoundsBase_ι_Round_ι_id , $ Л_stakeReward + $ Л_vestingReward , $ Л_newStake + $ Л_newVesting , $ Л_reinvest , $ Л_stakeFee + $ Л_vestingFee , $ Л_completedRound ^^ RoundsBase_ι_Round_ι_completionStatus )) ) >> 
 	 return $ Л_lastRound ) >> 
 	 
 >> return ; . 
 

Definition StakingContract_Ф__returnOrReinvest ( $ Л_completedRound : ι_Round )( $ Л_chunkSize : XInteger8 ) : StakingContractT ι_Round := 
 ( d1! RoundsBase_ι_Round_ι_stakes := $ Л_completedRound ^^ RoundsBase_ι_Round_ι_stakes ) >> 
 	 ( d0! Л_lastRound := RoundsBase_Ф__getLastRound () ) >> 
 	 ( d0! Л_sentMsgs := $ xInt0 ) >> 
 	 while (( ! empty () && $ Л_sentMsgs ?< $ Л_chunkSize ) { $ Л_sentMsgs ++ ) >> 
 	 (( $ Л_addr , $ Л_stake )) := delMin () ) >> 
 	 ( d0! Л_lastRound := StakingContract_Ф__returnOrReinvestForStakeholder (( $ Л_completedRound , $ Л_lastRound , $ Л_addr , $ Л_stake )) ) >> 
 	 
 } >> 
 
 Ift ( $ Л_completedRound ^^ RoundsBase_ι_Round_ι_id ?!= $ Л_lastRound ^^ RoundsBase_ι_Round_ι_id ) { RoundsBase_Ф__setLastRound (( $ Л_lastRound )) ) >> 
 	 
 } >> 
 ( d2! Л_completedRound ^^ RoundsBase_ι_Round_ι_step := empty () ? RoundsBase_ι_STEP_COMPLETED : RoundsBase_ι_STEP_COMPLETING ) >> 
 	 ( d2! Л_completedRound ^^ RoundsBase_ι_Round_ι_stakes := RoundsBase_ι_Round_ι_stakes ) >> 
 	 return $ Л_completedRound ) >> 
 	 
 >> return ; . 
 

Definition StakingContract_Ф__getStakeAndSendErrorIfNeeded ( msg_value : XInteger ) : StakingContractT XInteger64 # XBool := 
 $ xBoolTrue ) >> 
 	 ( d0! Л_msgValue := uint64 (( $ msg_value )) ) >> 
 	 ( d0! Л_minRequiredValue := StakingContract_ι_m_minStake + StakingContract_ι_ADD_STAKE_FEE ) >> 
 	 
 Ift ( $ Л_msgValue ?< $ Л_minRequiredValue ) { StakingContract_Ф__returnError (( StakingContract_ι_STATUS_STAKE_TOO_SMALL , $ Л_minRequiredValue )) ) >> 
 	 return (( $ xInt0 , $ xBoolFalse )) ) >> 
 	 
 } >> 
 
 Ift ( StakingContract_ι_m_poolClosed ) { StakingContract_Ф__returnError (( StakingContract_ι_STATUS_POOL_CLOSED , $ xInt0 )) ) >> 
 	 return (( $ xInt0 , $ xBoolFalse )) ) >> 
 	 
 } >> 
 
 Ift ( RoundsBase_Ф__getRoundsCount () ?== $ xInt0 ) { StakingContract_Ф__returnError (( StakingContract_ι_STATUS_NO_ACTIVE_ROUNDS , $ xInt0 )) ) >> 
 	 return (( $ xInt0 , $ xBoolFalse )) ) >> 
 	 
 } >> 
 return (( $ Л_msgValue - StakingContract_ι_ADD_STAKE_FEE , $ xBoolTrue )) ) >> 
 	 
 >> return ; . 
 

Definition StakingContract_Ф_addStake ( msg_sender : XInteger ) ( $ Л_reinvest : XBool ) : StakingContractT := 
 require (( $ msg_sender ?!= xInt0 , $ xInt108 )) ) >> 
 	 (( $ Л_stake , $ Л_ok )) := StakingContract_Ф__getStakeAndSendErrorIfNeeded () ) >> 
 	 
 Ift ( ! $ Л_ok ) { return ) >> 
 	 
 } >> 
 
 Ift ( ! StakingContract_Ф__investStake (( $ msg_sender , reinvest? $ Л_MAX_MONEY_VALUE : $ xInt0 , $ Л_stake , $ Л_reinvest )) ) { ( d0! Л_round := RoundsBase_Ф__getLastRound () ) >> 
 	 return StakingContract_Ф__returnError (( StakingContract_ι_STATUS_ROUND_STAKE_LIMIT , StakingContract_ι_m_maxRoundStake - $ Л_round ^^ RoundsBase_ι_Round_ι_stake )) ) >> 
 	 
 } >> 
 StakingContract_Ф__returnConfirmation (( StakingContract_ι_ADD_STAKE_FEE )) ) >> 
 	 
 >> return ; . 
 

Definition StakingContract_Ф_addVesting ( msg_sender : XInteger ) ( $ Л_dest : XAddress )( $ Л_withdrawalPeriod : XInteger32 )( $ Л_totalPeriod : XInteger32 ) : StakingContractT := 
 require (( $ Л_dest ^^ isStdAddrWithoutAnyCast () , $ xInt119 )) ) >> 
 	 
 Ift ( $ Л_dest ?== xInt0 ) { ( d0! Л_dest := $ msg_sender ) >> 
 	 
 } >> 
 (( $ Л_stake , $ Л_ok )) := StakingContract_Ф__getStakeAndSendErrorIfNeeded () ) >> 
 	 
 Ift ( ! $ Л_ok ) { return ) >> 
 	 
 } >> 
 ( d0! Л_round := RoundsBase_Ф__getLastRound () ) >> 
 	 
 Ift ( $ Л_round ^^ RoundsBase_ι_Round_ι_stake + $ Л_stake ?> StakingContract_ι_m_maxRoundStake ) { return StakingContract_Ф__returnError (( StakingContract_ι_STATUS_ROUND_STAKE_LIMIT , StakingContract_ι_m_maxRoundStake - $ Л_round ^^ RoundsBase_ι_Round_ι_stake )) ) >> 
 	 
 } >> 
 
 Ift ( $ Л_withdrawalPeriod ?> $ Л_totalPeriod ) { return StakingContract_Ф__returnError (( StakingContract_ι_STATUS_WITHDRAWAL_PERIOD_GREATER_TOTAL_PERIOD , $ xInt0 )) ) >> 
 	 
 } >> 
 
 Ift ( $ Л_totalPeriod ?>= $ xInt100 * (( $ Л_days )) ) { return StakingContract_Ф__returnError (( StakingContract_ι_STATUS_TOTAL_PERIOD_MORE_100YEARS , $ xInt0 )) ) >> 
 	 
 } >> 
 
 Ift ( $ Л_withdrawalPeriod ?== $ xInt0 ) { return StakingContract_Ф__returnError (( StakingContract_ι_STATUS_WITHDRAWAL_PERIOD_IS_ZERO , $ xInt0 )) ) >> 
 	 
 } >> 
 
 Ift ( $ Л_totalPeriod $ Л_% $ Л_withdrawalPeriod ?!= $ xInt0 ) { return StakingContract_Ф__returnError (( StakingContract_ι_STATUS_TOTAL_PERIOD_IS_NOT_DIVED_BY_WITHDRAWAL_PERIOD , $ xInt0 )) ) >> 
 	 
 } >> 
 ( d0! Л_stakeholder := StakeholderBase_Ф__getStakeholder (( $ Л_dest )) ) >> 
 	 
 Ift ( StakeholderBase_Ф__haveVesting (( $ Л_stakeholder )) ) { return StakingContract_Ф__returnError (( StakingContract_ι_STATUS_STAKEHOLDER_HAVE_ALREADY_VESTING , $ xInt0 )) ) >> 
 	 
 } >> 
 ( d0! Л_periodPayment := uint64 (( uint (( $ Л_stake )) * $ Л_withdrawalPeriod / $ Л_totalPeriod )) ) >> 
 	 
 Ift ( $ Л_periodPayment ?== $ xInt0 ) { return StakingContract_Ф__returnError (( StakingContract_ι_STATUS_PERIOD_PAYMENT_IS_ZERO , $ xInt0 )) ) >> 
 	 
 } >> 
 ( d0! Л_stakeholder := StakeholderBase_Ф__stakeholderSetVesting (( $ Л_stakeholder , $ Л_stake , $ Л_withdrawalPeriod , $ Л_periodPayment , $ msg_sender )) ) >> 
 	 StakeholderBase_Ф__setOrDeleteStakeholder (( $ Л_dest , $ Л_stakeholder )) ) >> 
 	 RoundsBase_Ф__setLastRound (( RoundsBase_Ф__roundAddStakeAndVesting (( $ Л_round , $ Л_dest , $ xInt0 , $ Л_stake )) )) ) >> 
 	 StakingContract_Ф__returnConfirmation (( StakingContract_ι_ADD_STAKE_FEE )) ) >> 
 	 
 >> return ; . 
 

Definition StakingContract_Ф_removeStake ( msg_value : XInteger ) ( msg_sender : XInteger ) ( $ Л_stake : XInteger64 ) : StakingContractT := 
 require (( $ msg_sender ?!= xInt0 , $ xInt108 )) ) >> 
 	 
 Ift ( $ msg_value ?< StakingContract_ι_REMOVE_STAKE_FEE ) { StakingContract_Ф__returnError (( StakingContract_ι_STATUS_MSG_VAL_TOO_SMALL , StakingContract_ι_REMOVE_STAKE_FEE )) ) >> 
 	 return ) >> 
 	 
 } >> 
 ( d0! Л_member := StakeholderBase_Ф__getStakeholder (( $ msg_sender )) ) >> 
 	 ( d0! Л_removedStake := tvm_min (( $ Л_stake , $ Л_member ^^ StakeholderBase_ι_Stakeholder_ι_unusedStake )) ) >> 
 	 StakeholderBase_Ф__stakeholderRemoveStake (( $ msg_sender , $ Л_removedStake , $ Л_removedStake )) ) >> 
 	 $ msg_sender ^^ transfer (( $ Л_removedStake , $ xBoolTrue , $ xInt3 )) ) >> 
 	 
 >> return ; . 
 

Definition StakingContract_Ф_continueStake ( msg_value : XInteger ) ( msg_sender : XInteger ) ( $ Л_amount : XInteger64 )( $ Л_reinvest : XBool ) : StakingContractT := 
 require (( $ msg_sender ?!= xInt0 , $ xInt108 )) ) >> 
 	 
 Ift ( $ msg_value ?< StakingContract_ι_CONTINUE_STAKE_FEE ) { return StakingContract_Ф__returnError (( StakingContract_ι_STATUS_MSG_VAL_TOO_SMALL , StakingContract_ι_CONTINUE_STAKE_FEE )) ) >> 
 	 
 } >> 
 
 Ift ( ! StakeholderBase_Ф__stakeholderExists (( $ msg_sender )) ) { return StakingContract_Ф__returnError (( StakingContract_ι_STATUS_NO_STAKE , $ xInt0 )) ) >> 
 	 
 } >> 
 
 Ift ( ! StakingContract_Ф__investStake (( $ msg_sender , $ Л_amount ?== 0? $ Л_MAX_MONEY_VALUE : $ Л_amount , $ xInt0 , $ Л_reinvest )) ) { ( d0! Л_round := RoundsBase_Ф__getLastRound () ) >> 
 	 return StakingContract_Ф__returnError (( StakingContract_ι_STATUS_ROUND_STAKE_LIMIT , StakingContract_ι_m_maxRoundStake - $ Л_round ^^ RoundsBase_ι_Round_ι_stake )) ) >> 
 	 
 } >> 
 StakingContract_Ф__returnConfirmation (( StakingContract_ι_CONTINUE_STAKE_FEE )) ) >> 
 	 
 >> return ; . 
 

Definition StakingContract_Ф_setReinvest ( msg_sender : XInteger ) ( $ Л_flag : XBool ) : StakingContractT := 
 require (( $ msg_sender ?!= xInt0 , $ xInt108 )) ) >> 
 	 ( d0! Л_sender := $ msg_sender ) >> 
 	 require (( StakeholderBase_Ф__stakeholderExists (( $ Л_sender )) , $ xInt101 )) ) >> 
 	 StakeholderBase_Ф__stakeholderSetReinvest (( $ Л_sender , $ Л_flag )) ) >> 
 	 
 >> return ; . 
 

Definition StakingContract_Ф_transferStake ( msg_value : XInteger ) ( msg_sender : XInteger ) ( $ Л_destination : XAddress )( $ Л_amount : XInteger64 ) : StakingContractT := 
 require (( $ msg_sender ?!= xInt0 , $ xInt108 )) ) >> 
 	 ( d0! Л_sender := $ msg_sender ) >> 
 	 (( $ Л_exists , $ Л_donor )) := StakeholderBase_Ф__stakeholderFetch (( $ Л_sender )) ) >> 
 	 require (( $ Л_exists , $ xInt101 )) ) >> 
 	 require (( $ Л_destination ^^ isStdAddrWithoutAnyCast () && ! $ Л_destination ^^ isStdZero () , $ xInt119 )) ) >> 
 	 
 Ift ( $ msg_value ?< StakingContract_ι_TRANSFER_STAKE_FEE ) { return StakingContract_Ф__returnError (( StakingContract_ι_STATUS_MSG_VAL_TOO_SMALL , StakingContract_ι_TRANSFER_STAKE_FEE )) ) >> 
 	 
 } >> 
 
 Ift ( ! RoundsBase_Ф_arePendingRoundsEmpty () ) { return StakingContract_Ф__returnError (( StakingContract_ι_STATUS_NO_TRANSFER_WHILE_PENDING_ROUND , $ xInt0 )) ) >> 
 	 
 } >> 
 
 Ift ( StakingContract_ι_m_poolClosed ) { return StakingContract_Ф__returnError (( StakingContract_ι_STATUS_POOL_CLOSED , $ xInt0 )) ) >> 
 	 
 } >> 
 
 Ift ( $ Л_amount ?== $ xInt0 ) { ( d0! Л_amount := StakingContract_ι_MAX_MONEY_VALUE ) >> 
 	 
 } >> 
 ( d0! Л_receiver := StakeholderBase_Ф__getStakeholder (( $ Л_destination )) ) >> 
 	 ( d0! Л_transferredStake := RoundsBase_Ф__roundMoveStakes (( $ Л_sender , $ Л_destination , $ Л_amount )) ) >> 
 	 ( d0! Л_transferredUnused := tvm_min (( $ Л_amount - $ Л_transferredStake , $ Л_donor ^^ StakeholderBase_ι_Stakeholder_ι_unusedStake )) ) >> 
 	 ( d0! Л_transferred := $ Л_transferredStake + $ Л_transferredUnused ) >> 
 	 ( d0! Л_donor := StakeholderBase_Ф__stakeholderDecreaseTotalAndUnused (( $ Л_donor , $ Л_transferred , $ Л_transferredUnused )) ) >> 
 	 ( d0! Л_receiver := StakeholderBase_Ф__stakeholderIncreaseTotalAndUnused (( $ Л_receiver , $ Л_transferred , $ Л_transferredUnused )) ) >> 
 	 StakeholderBase_Ф__setOrDeleteStakeholder (( $ Л_sender , $ Л_donor )) ) >> 
 	 StakeholderBase_Ф__setOrDeleteStakeholder (( $ Л_destination , $ Л_receiver )) ) >> 
 	 StakingContract_Ф__returnConfirmation (( StakingContract_ι_TRANSFER_STAKE_FEE )) ) >> 
 	 
 >> return ; . 
 

Definition StakingContract_Ф_processNewStake ( msg_sender : XInteger ) ( $ Л_queryId : XInteger64 )( $ Л_validatorKey : XInteger256 )( $ Л_stakeAt : XInteger32 )( $ Л_maxFactor : XInteger32 )( $ Л_adnlAddr : XInteger256 )( $ Л_signature : XInteger8 ) : StakingContractT := 
 require (( StakingContract_ι_Node_ι_wallet ?== $ msg_sender , $ xInt113 )) ) >> 
 	 ( d0! Л_request := ElectorBase_ι_Request (( $ Л_queryId , $ Л_validatorKey , $ Л_stakeAt , $ Л_maxFactor , $ Л_adnlAddr , $ Л_signature )) ) >> 
 	 StakingContract_Ф__addRequest (( $ Л_stakeAt , $ Л_request )) ) >> 
 	 
 Ife ( $ Л_stakeAt ?== ElectionParams_Ф__getElectAt () ) { 
 } 
 else 
 { 
 require (( RoundsBase_Ф__getRoundsCount () ?>= $ xInt2 , $ xInt111 )) ) >> 
 	 ( d0! Л_round := RoundsBase_Ф__getPenultimateRound () ) >> 
 	 require (( $ Л_round ^^ RoundsBase_ι_Round_ι_step ?== RoundsBase_ι_STEP_WAITING_REQUESTS , $ xInt118 )) ) >> 
 	 require (( $ Л_stakeAt ?== $ Л_round ^^ RoundsBase_ι_Round_ι_id , $ xInt111 )) ) >> 
 	 ElectorBase_Ф__runForElection (( $ Л_request , RoundsBase_ι_Round_ι_stake )) ) >> 
 	 ( d2! Л_round ^^ RoundsBase_ι_Round_ι_step := RoundsBase_ι_STEP_ELECTIONS ) >> 
 	 RoundsBase_Ф__setPenultimateRound (( $ Л_round )) ) >> 
 	 
 } >> 
 StakingContract_Ф__returnGrams () ) >> 
 	 
 >> return ; . 
 

Definition StakingContract_Ф_ticktock ( msg_sender : XInteger ) : StakingContractT := 
 require (( $ msg_sender ?!= xInt0 , $ xInt108 )) ) >> 
 	 ( d0! Л_electionsStarted := now ?>= ElectionParams_Ф__getElectionsStart () ) >> 
 	 
 Ife ( $ Л_electionsStarted ) { StakingContract_Ф__addNewRoundAndUpdateRounds () ) >> 
 	 
 } 
 else 
 Ife ( RoundsBase_Ф__getRoundsCount () ?< $ xInt2 ) { 
 Ife ( RoundsBase_Ф__getRoundsCount () ?== $ xInt0 )) StakingContract_Ф__addNewRoundAndUpdateRounds () ) >> 
 	 
 } 
 else 
 Ife ( StakingContract_Ф__checkPenultimateRound () ) { 
 } 
 else 
 Ift ( StakingContract_Ф__checkOldestRound () ) { 
 } >> 
 StakingContract_Ф__returnGrams () ) >> 
 	 
 >> return ; . 
 

Definition StakingContract_Ф_forceCompletePendingRound ( msg_sender : XInteger ) ( $ Л_doCompleteOneChunk : XBool )( $ Л_chunkSize : XInteger8 ) : StakingContractT := 
 require (( $ msg_sender ?!= xInt0 , $ xInt108 )) ) >> 
 	 (( _ , $ Л_round , $ Л_ok )) := RoundsBase_Ф__fetchOldestPendingRound () ) >> 
 	 require (( $ Л_ok , $ xInt121 )) ) >> 
 	 require (( $ Л_round ^^ RoundsBase_ι_Round_ι_end + $ xInt1 $ Л_hours ?< now , $ xInt122 )) ) >> 
 	 tvm_accept () ) >> 
 	 
 Ife ( $ Л_doCompleteOneChunk ) { ( d0! Л_round := StakingContract_Ф__returnOrReinvest (( $ Л_round , $ Л_chunkSize )) ) >> 
 	 
 } 
 else 
 { 
 ( d0! Л_round := StakingContract_Ф__completePendingRound (( $ Л_round , $ Л_chunkSize )) ) >> 
 	 
 } >> 
 RoundsBase_Ф__setOrDeletePendingRound (( $ Л_round )) ) >> 
 	 
 >> return ; . 
 

Definition StakingContract_Ф_completePendingRoundChunk ( msg_sender : XInteger ) ( $ Л_roundId : XInteger32 )( $ Л_chunkSize : XInteger8 ) : StakingContractT := 
 require (( $ msg_sender ?== address(this) , $ xInt120 )) ) >> 
 	 (( $ Л_exists , $ Л_round )) := RoundsBase_Ф__roundFetchPendingRound (( $ Л_roundId )) ) >> 
 	 
 Ift ( $ Л_exists ) { tvm_accept () ) >> 
 	 RoundsBase_Ф__setOrDeletePendingRound (( StakingContract_Ф__returnOrReinvest (( $ Л_round , $ Л_chunkSize )) )) ) >> 
 	 
 } >> 
 
 >> return ; . 
 

Definition StakingContract_Ф_receiveReturnedStake ( $ Л_queryId : XInteger64 )( $ Л_comment : XInteger32 ) : StakingContractT XInteger64 # XInteger32 := 
 ( d0! Л_round := RoundsBase_Ф__getPenultimateRound () ) >> 
 	 ( d2! Л_round ^^ RoundsBase_ι_Round_ι_completionStatus := RoundsBase_ι_ROUND_STAKE_REJECTED ) >> 
 	 RoundsBase_Ф__setPenultimateRound (( StakingContract_Ф__completeRound (( RoundsBase_Ф__getPenultimateRound () , StakingContract_ι_MAX_MSGS_PER_TR )) )) ) >> 
 	 return (( $ Л_queryId , $ Л_comment )) ) >> 
 	 
 >> return ; . 
 

Definition StakingContract_Ф_acceptRecoveredStake ( msg_sender : XInteger ) ( $ Л_queryId : XInteger64 ) : StakingContractT := 
 require (( $ msg_sender ?== ElectorBase_ι_m_elector , $ xInt107 )) ) >> 
 	 
 Ife ( $ Л_queryId ?== $ xInt0 ) { StakingContract_Ф__acceptUnusedStake () ) >> 
 	 
 } 
 else 
 Ife ( $ Л_queryId ?== $ xInt1 ) { StakingContract_Ф__acceptRewardStake () ) >> 
 	 
 } 
 else 
 { 
 StakingContract_Ф__acceptPendingRoundStake (( uint32 (( $ Л_queryId )) )) ) >> 
 	 
 } >> 
 
 >> return ; . 
 

Definition StakingContract_Ф_terminator ( $ Л_chunkSize : XInteger8 ) : StakingContractT := 
 require (( $ msg_pubkey () ?== tvm_pubkey () , $ xInt300 )) ) >> 
 	 require (( ! StakingContract_ι_m_poolClosed , $ xInt114 )) ) >> 
 	 ( d1! StakingContract_ι_m_poolClosed := $ xBoolTrue ) >> 
 	 tvm_accept () ) >> 
 	 
 Ift ( RoundsBase_Ф__getRoundsCount () ?!= $ xInt0 ) { ( d0! Л_lastRound := RoundsBase_Ф__getLastRound () ) >> 
 	 ( d2! Л_lastRound ^^ RoundsBase_ι_Round_ι_completionStatus := RoundsBase_ι_ROUND_POOL_CLOSED ) >> 
 	 RoundsBase_Ф__setLastRound (( StakingContract_Ф__completeRound (( $ Л_lastRound , $ Л_chunkSize )) )) ) >> 
 	 
 } >> 
 emit $ Л_stakingPoolClosed () ) >> 
 	 
 >> return ; . 
 

Definition DePool_Ф_getRounds : DePoolT XInteger32 # XInteger32 # ι_М_RoundInfo := 
 RoundsBase_Ф__getRoundsInfo () ) >> 
 	 RoundsBase_Ф__getRoundsCount () ) >> 
 	 ElectionParams_Ф__getElectAt () ) >> 
 	 
 >> return ; . 
 

Definition DePool_Ф_getStakeholderInfo ( $ Л_addr : XAddress ) : DePoolT XInteger64 # XInteger64 # XInteger64 # XBool # XInteger64 # ι_М_StakeInfo := 
 require (( StakeholderBase_Ф__stakeholderExists (( $ Л_addr )) , $ xInt116 )) ) >> 
 	 ( d0! Л_stakeholder := StakeholderBase_Ф__getStakeholder (( $ Л_addr )) ) >> 
 	 ( d1! StakeholderBase_ι_Stakeholder_ι_reinvest := $ Л_stakeholder ^^ StakeholderBase_ι_Stakeholder_ι_reinvest ) >> 
 	 $ Л_stakeholder ^^ StakeholderBase_ι_Stakeholder_ι_totalStake ) >> 
 	 ( d1! OwnerBase_ι_Owner_ι_reward := $ Л_stakeholder ^^ StakeholderBase_ι_Stakeholder_ι_grossReward ) >> 
 	 $ Л_stakeholder ^^ StakeholderBase_ι_Stakeholder_ι_unusedStake ) >> 
 	 total - available ) >> 
 	 ( d0! Л_invested2 := $ xInt0 ) >> 
 	 (( $ Л_index , $ Л_round , $ Л_ok )) := min () ) >> 
 	 while (( $ Л_ok ) { 
 Ife ( $ Л_round ^^ RoundsBase_ι_Round_ι_step ?< RoundsBase_ι_STEP_COMPLETED ) { (( $ Л_presents , $ Л_value )) := $ Л_round ^^ RoundsBase_ι_Round_ι_stakes . fetch (( $ Л_addr )) ) >> 
 	 
 Ift ( $ Л_presents ) { push (( DePool_ι_StakeInfo (( $ Л_round ^^ RoundsBase_ι_Round_ι_id , $ Л_value ^^ RoundsBase_ι_StakeValue_ι_simple , $ Л_value ^^ RoundsBase_ι_StakeValue_ι_vesting )) )) ) >> 
 	 ( d0! Л_invested2 += $ Л_value ^^ RoundsBase_ι_StakeValue_ι_simple + $ Л_value ^^ RoundsBase_ι_StakeValue_ι_vesting ) >> 
 	 
 } >> 
 
 } 
 else 
 { 
 (( $ Л_presents , $ Л_value )) := $ Л_round ^^ RoundsBase_ι_Round_ι_stakes . fetch (( $ Л_addr )) ) >> 
 	 
 Ift ( $ Л_presents ) { ( d0! Л_invested2 += $ Л_value ^^ RoundsBase_ι_StakeValue_ι_simple + $ Л_value ^^ RoundsBase_ι_StakeValue_ι_vesting ) >> 
 	 
 } >> 
 
 } >> 
 (( $ Л_index , $ Л_round , $ Л_ok )) := next (( $ Л_index )) ) >> 
 	 
 } >> 
 (( $ Л_index , $ Л_round , $ Л_ok )) := min () ) >> 
 	 while (( $ Л_ok ) { (( $ Л_presents , $ Л_value )) := $ Л_round ^^ RoundsBase_ι_Round_ι_stakes . fetch (( $ Л_addr )) ) >> 
 	 
 Ift ( $ Л_presents ) { ( d0! Л_invested2 += $ Л_value ^^ RoundsBase_ι_StakeValue_ι_simple + $ Л_value ^^ RoundsBase_ι_StakeValue_ι_vesting ) >> 
 	 
 } >> 
 (( $ Л_index , $ Л_round , $ Л_ok )) := next (( uint32 (( $ Л_index )) )) ) >> 
 	 
 } >> 
 
 >> return ; . 
 

Definition DePool_Ф_getStakingInfo : DePoolT XInteger64 # XInteger64 # XInteger64 # XInteger64 # XInteger32 # XInteger64 # XInteger64 # XInteger64 # XInteger64 # XInteger64 # XInteger64 # XInteger64 := 
 StakingContract_ι_m_minStake ) >> 
 	 StakingContract_ι_m_minRoundStake ) >> 
 	 StakingContract_ι_m_maxRoundStake ) >> 
 	 ElectionParams_Ф__getStakingPeriod () ) >> 
 	 StakingContract_ι_m_lastRoundInterest ) >> 
 	 StakingContract_ι_NOTIFY_FEE ) >> 
 	 StakingContract_ι_ADD_STAKE_FEE ) >> 
 	 StakingContract_ι_REMOVE_STAKE_FEE ) >> 
 	 StakingContract_ι_PAUSE_STAKE_FEE ) >> 
 	 StakingContract_ι_CONTINUE_STAKE_FEE ) >> 
 	 StakingContract_ι_SET_REINVEST_FEE ) >> 
 	 (( StakingContract_ι_m_minRoundStake * StakingContract_ι_NODE_WALLET_MIN_STAKE )) / $ xInt100 ) >> 
 	 
 >> return ; . 
 

Definition DePool_Ф_getPendingRounds : DePoolT ι_М_RoundInfo := 
 RoundsBase_Ф__getPendingRoundsInfo () ) >> 
 	 
 >> return ; . 
 

Definition StakingProxyContract_Ф_process_new_stake ( msg_value : XInteger ) ( msg_sender : XInteger ) ( $ Л_queryId : XInteger64 )( $ Л_validatorKey : XInteger256 )( $ Л_stakeAt : XInteger32 )( $ Л_maxFactor : XInteger32 )( $ Л_adnlAddr : XInteger256 )( $ Л_signature : XInteger8 ) : StakingProxyContractT := 
 require (( $ msg_sender ?== StakingProxyContract_ι_m_staking , $ xInt102 )) ) >> 
 	 IElector (( ElectorBase_ι_m_elector )) . _Ф_elector_process_new_stake ^^ value (( $ msg_value - StakingProxyContract_ι_PROXY_FEE )) (( $ Л_queryId , $ Л_validatorKey , $ Л_stakeAt , $ Л_maxFactor , $ Л_adnlAddr , $ Л_signature )) ) >> 
 	 
 >> return ; . 
 

Definition ElectionParams_Ф_Constructor4 ( $ Л_electionId : XInteger32 )( $ Л_beginBefore : XInteger32 )( $ Л_endBefore : XInteger32 )( $ Л_heldFor : XInteger32 )( $ Л_electedFor : XInteger32 ) : ElectionParamsT := 
 
 Ife ( $ Л_electionId ?!= $ xInt0 ) { ( d1! ElectionParams_ι_m_electAt := $ Л_electionId ) >> 
 	 
 } 
 else 
 { 
 ( d1! ElectionParams_ι_m_electAt := ElectionParams_Ф__getNextElectionId () ) >> 
 	 
 } >> 
 (( ElectionParams_ι_m_electedFor , ElectionParams_ι_m_beginBefore , ElectionParams_ι_m_endBefore , ElectionParams_ι_m_heldFor , $ Л_ok )) := tvm_configParam (( $ xInt15 )) ) >> 
 	 
 Ift ( ! $ Л_ok ) { ( d1! ElectionParams_ι_m_beginBefore := $ Л_beginBefore ) >> 
 	 ( d1! ElectionParams_ι_m_endBefore := $ Л_endBefore ) >> 
 	 ( d1! ElectionParams_ι_m_electedFor := $ Л_electedFor ) >> 
 	 ( d1! ElectionParams_ι_m_heldFor := $ Л_heldFor ) >> 
 	 
 } >> 
 
 >> return ; . 
 

Definition StakingOwner_Ф_initTimer ( $ Л_timer : XAddress )( $ Л_period : XInteger ) : StakingOwnerT := 
 require (( $ msg_pubkey () ?== tvm_pubkey () , $ xInt101 )) ) >> 
 	 ( d1! StakingOwner_ι_m_timer := $ Л_timer ) >> 
 	 ( d1! StakingOwner_ι_m_timeout := $ Л_period ) >> 
 	 StakingOwner_Ф__settimer (( $ Л_timer , $ Л_period )) ) >> 
 	 
 >> return ; . 
 

Definition StakingOwner_Ф_upgrade ( $ Л_newcode : TvmCell ) : StakingOwnerT := 
 require (( $ msg_pubkey () ?== tvm_pubkey () , $ xInt101 )) ) >> 
 	 tvm_commit () ) >> 
 	 tvm_setcode (( $ Л_newcode )) ) >> 
 	 tvm_setCurrentCode (( $ Л_newcode )) ) >> 
 	 StakingOwner_Ф_onCodeUpgrade () ) >> 
 	 
 >> return ; . 
 

Definition RoundsBase_Ф__roundMoveStakes ( $ Л_source : XAddress )( $ Л_destination : XAddress )( $ Л_targetAmount : XInteger64 ) : RoundsBaseT XInteger64 := 
 (( $ Л_roundId , $ Л_round , $ Л_ok )) := min () ) >> 
 	 ( d0! Л_transferred := $ xInt0 ) >> 
 	 while (( $ Л_ok && $ Л_targetAmount ?!= $ xInt0 ) { 
 Ift ( $ Л_round ^^ RoundsBase_ι_Round_ι_step ?!= RoundsBase_ι_STEP_COMPLETED && $ Л_round ^^ RoundsBase_ι_Round_ι_step ?!= RoundsBase_ι_STEP_COMPLETING ) { (( RoundsBase_ι_m_rounds [ $ Л_roundId ] , $ Л_currentTransferred )) := RoundsBase_Ф__roundMoveStake (( $ Л_round , $ Л_source , $ Л_destination , $ Л_targetAmount )) ) >> 
 	 ( d0! Л_targetAmount -= $ Л_currentTransferred ) >> 
 	 ( d0! Л_transferred += $ Л_currentTransferred ) >> 
 	 
 } >> 
 (( $ Л_roundId , $ Л_round , $ Л_ok )) := next (( $ Л_roundId )) ) >> 
 	 
 } >> 
 return $ Л_transferred ) >> 
 	 
 >> return ; . 
 

Definition StakingContract_Ф__completePendingRound ( $ Л_pendingRound : ι_Round )( $ Л_chunkSize : XInteger8 ) : StakingContractT ι_Round := 
 
 Ife ( $ Л_pendingRound ^^ RoundsBase_ι_Round_ι_participantQty ?> $ Л_chunkSize ) { for (( ( d0! Л_i := $ xInt0 ) >> 
 	 $ Л_i ?< $ Л_pendingRound ^^ RoundsBase_ι_Round_ι_participantQty ) >> 
 	 ( d0! Л_i += $ Л_chunkSize ) { this ^^ StakingContract_Ф_completePendingRoundChunk . value (( 1e7 )) (( $ Л_pendingRound ^^ RoundsBase_ι_Round_ι_id , $ Л_chunkSize )) ) >> 
 	 
 } >> 
 
 } 
 else 
 { 
 ( d0! Л_pendingRound := StakingContract_Ф__returnOrReinvest (( $ Л_pendingRound , $ Л_chunkSize )) ) >> 
 	 
 } >> 
 return $ Л_pendingRound ) >> 
 	 
 >> return ; . 
 

