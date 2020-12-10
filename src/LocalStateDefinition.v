Record LocalStateP := LocalStateC  
{ 
LocalState_ι__addStakes_Л_participant : DePoolLib_ι_ParticipantP ; 
LocalState_ι__addStakes_Л_round : RoundsBase_ι_RoundP  ; 
LocalState_ι__addStakes_Л_sv :  RoundsBase_ι_StakeValueP  ;

LocalState_ι__returnOrReinvestForParticipant_Л_attachedValue : I64 ; 
LocalState_ι__returnOrReinvestForParticipant_Л_newLock : M RoundsBase_ι_InvestParamsP   ; 
LocalState_ι__returnOrReinvestForParticipant_Л_newStake : I64 ; 
LocalState_ι__returnOrReinvestForParticipant_Л_newVesting : M RoundsBase_ι_InvestParamsP   ; 
LocalState_ι__returnOrReinvestForParticipant_Л_participant :  DePoolLib_ι_ParticipantP ;
LocalState_ι__returnOrReinvestForParticipant_Л_reward : I64 ; 
LocalState_ι__returnOrReinvestForParticipant_Л_round0 : RoundsBase_ι_RoundP  ;

(* LocalState_ι__returnOrReinvest_Л_chunkSize : I8  ; *)
LocalState_ι__returnOrReinvest_Л_round2 :  RoundsBase_ι_RoundP   ; 
LocalState_ι__returnOrReinvest_Л_round0 : RoundsBase_ι_RoundP  ; 
LocalState_ι__returnOrReinvest_Л_startIndex : I ;

LocalState_ι_addVestingOrLock_Л_participant : DePoolLib_ι_ParticipantP ;
LocalState_ι_addVestingOrLock_Л_l : M  RoundsBase_ι_InvestParamsP  ;
LocalState_ι_addVestingOrLock_Л_v : M  RoundsBase_ι_InvestParamsP  ;

LocalState_ι_completeRound_Л_i : I ;
LocalState_ι_completeRound_Л_msgQty : I ;
LocalState_ι_completeRound_Л_restParticipant : I32  ; 

LocalState_ι_cutWithdrawalValue_Л_p : RoundsBase_ι_InvestParamsP   ; 
LocalState_ι_cutWithdrawalValue_Л_withdrawal : I64  ;

LocalState_ι_getRounds_Л_pair : M (P I64 RoundsBase_ι_RoundP) ;
LocalState_ι_getRounds_Л_rounds : HM I64 RoundsBase_ι_TruncatedRoundP  ;

LocalState_ι_onFailToRecoverStake_Л_round :  RoundsBase_ι_RoundP   ;

LocalState_ι_onSuccessToRecoverStake_Л_round : RoundsBase_ι_RoundP   ;

LocalState_ι_terminator_Л_round1 : RoundsBase_ι_RoundP   ; 

LocalState_ι_transferStakeInOneRound_Л_deltaDestinationStake : I64  ;
LocalState_ι_transferStakeInOneRound_Л_destinationParticipant : DePoolLib_ι_ParticipantP   ;
LocalState_ι_transferStakeInOneRound_Л_newSourceStake : I64 ;
LocalState_ι_transferStakeInOneRound_Л_round : RoundsBase_ι_RoundP  ; 
LocalState_ι_transferStakeInOneRound_Л_sourceParticipant : DePoolLib_ι_ParticipantP  ;
LocalState_ι_transferStakeInOneRound_Л_sourceStake : RoundsBase_ι_StakeValueP  ;

LocalState_ι_transferStake_Л_amount : I64  ;
LocalState_ι_transferStake_Л_destParticipant : DePoolLib_ι_ParticipantP  ;
LocalState_ι_transferStake_Л_pair : M (P I64  RoundsBase_ι_RoundP)  ;  
LocalState_ι_transferStake_Л_rounds : HM I64 RoundsBase_ι_RoundP   ;  
LocalState_ι_transferStake_Л_srcParticipant : DePoolLib_ι_ParticipantP ;
LocalState_ι_transferStake_Л_totalSrcStake : I64;
LocalState_ι_transferStake_Л_transferred : I64 ;

LocalState_ι_updateRound2_Л_round2 :  RoundsBase_ι_RoundP   ; 

LocalState_ι_updateRounds_Л_round0 :  RoundsBase_ι_RoundP   ; 
LocalState_ι_updateRounds_Л_round1 :  RoundsBase_ι_RoundP   ; 
LocalState_ι_updateRounds_Л_round2 :  RoundsBase_ι_RoundP   ; 

LocalState_ι_withdrawStakeInPoolingRound_Л_participant : DePoolLib_ι_ParticipantP  ;
LocalState_ι_withdrawStakeInPoolingRound_Л_round :  RoundsBase_ι_RoundP  ;
LocalState_ι_withdrawStakeInPoolingRound_Л_sv : RoundsBase_ι_StakeValueP ;
LocalState_ι_withdrawStakeInPoolingRound_Л_targetAmount : I64 ;

LocalState_ι_constructor5_Л_ok : B ;

LocalState_ι__returnOrReinvestForParticipant_Л_round2 : RoundsBase_ι_RoundP ;
LocalState_ι__returnOrReinvestForParticipant_Л_lostFunds : I64 ;
LocalState_ι__returnOrReinvestForParticipant_Л_params : RoundsBase_ι_InvestParamsP ;

LocalState_ι_totalParticipantFunds_Л_stakes : I64 ;
LocalState_ι_totalParticipantFunds_Л_pair :  M (P I64 RoundsBase_ι_RoundP) ;

LocalState_ι_updateRounds_Л_roundPre0 : RoundsBase_ι_RoundP ;
LocalState_ι_cutDePoolReward_Л_reward : I64 ;
LocalState_ι_onBounce_Л_optRound : M RoundsBase_ι_RoundP ;

LocalState_ι_startRoundCompleting_Л_round : RoundsBase_ι_RoundP ;

LocalState_ι_cutWithdrawalValue_Л_withdrawalTons : I64 ;
LocalState_ι_cutWithdrawalValue_Л_tonsForOwner : I64 ;

LocalState_ι_constructor6_Л_proxy : A

} .

(* Arguments LocalStateC [ I I64 A C B I256 I32 I8 I128 I16 HM P M L ] . *)