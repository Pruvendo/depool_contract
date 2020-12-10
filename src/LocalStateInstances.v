
(* (I I8 I32 I64 I256 A B : Type) (L M : Type -> Type) (HM P : Type -> Type -> Type)  *)
Definition LocalState := @LocalStateP XInteger XInteger8 XInteger32 XInteger64 XInteger256 XAddress XBool  XList XMaybe XHMap XProd. 
Global Instance Struct_LocalState : Struct LocalState :=  { 
 	fields :=  [ 
 		@existT _ _ _  LocalState_ι__addStakes_Л_participant ,
 		@existT _ _ _  LocalState_ι__addStakes_Л_round  ,
		 @existT _ _ _  LocalState_ι__addStakes_Л_sv ,
		 
 		@existT _ _ _  LocalState_ι__returnOrReinvestForParticipant_Л_attachedValue , 
 		@existT _ _ _  LocalState_ι__returnOrReinvestForParticipant_Л_newLock ,
 		@existT _ _ _  LocalState_ι__returnOrReinvestForParticipant_Л_newStake ,
 		@existT _ _ _  LocalState_ι__returnOrReinvestForParticipant_Л_newVesting  ,
 		@existT _ _ _  LocalState_ι__returnOrReinvestForParticipant_Л_participant ,
 		@existT _ _ _  LocalState_ι__returnOrReinvestForParticipant_Л_reward ,
 		@existT _ _ _  LocalState_ι__returnOrReinvestForParticipant_Л_round0 ,
		 
(*  		@existT _ _ _  LocalState_ι__returnOrReinvest_Л_chunkSize ,*) 		@existT _ _ _  LocalState_ι__returnOrReinvest_Л_round2 ,
 		@existT _ _ _  LocalState_ι__returnOrReinvest_Л_round0  ,
 		@existT _ _ _  LocalState_ι__returnOrReinvest_Л_startIndex ,
		 
 		@existT _ _ _  LocalState_ι_addVestingOrLock_Л_participant ,
 		@existT _ _ _  LocalState_ι_addVestingOrLock_Л_l,
 		@existT _ _ _  LocalState_ι_addVestingOrLock_Л_v ,
		 
 		@existT _ _ _  LocalState_ι_completeRound_Л_i ,
 		@existT _ _ _  LocalState_ι_completeRound_Л_msgQty ,
		 @existT _ _ _  LocalState_ι_completeRound_Л_restParticipant  ,
		 
 		@existT _ _ _  LocalState_ι_cutWithdrawalValue_Л_p ,
		 @existT _ _ _  LocalState_ι_cutWithdrawalValue_Л_withdrawal ,
		 
 		@existT _ _ _  LocalState_ι_getRounds_Л_pair ,
		 @existT _ _ _  LocalState_ι_getRounds_Л_rounds ,
		 
 		@existT _ _ _  LocalState_ι_onFailToRecoverStake_Л_round ,
 		@existT _ _ _  LocalState_ι_onSuccessToRecoverStake_Л_round ,
		 @existT _ _ _  LocalState_ι_terminator_Л_round1 ,
		 
 		@existT _ _ _  LocalState_ι_transferStakeInOneRound_Л_deltaDestinationStake ,
 		@existT _ _ _  LocalState_ι_transferStakeInOneRound_Л_destinationParticipant ,
 		@existT _ _ _  LocalState_ι_transferStakeInOneRound_Л_newSourceStake ,
 		@existT _ _ _  LocalState_ι_transferStakeInOneRound_Л_round ,
 		@existT _ _ _  LocalState_ι_transferStakeInOneRound_Л_sourceParticipant ,
		 @existT _ _ _  LocalState_ι_transferStakeInOneRound_Л_sourceStake ,
		 
 		@existT _ _ _  LocalState_ι_transferStake_Л_amount,
 		@existT _ _ _  LocalState_ι_transferStake_Л_destParticipant ,
 		@existT _ _ _  LocalState_ι_transferStake_Л_pair  ,
 		@existT _ _ _  LocalState_ι_transferStake_Л_rounds ,
 		@existT _ _ _  LocalState_ι_transferStake_Л_srcParticipant ,
 		@existT _ _ _  LocalState_ι_transferStake_Л_totalSrcStake,
		 @existT _ _ _  LocalState_ι_transferStake_Л_transferred ,
		 
		 @existT _ _ _  LocalState_ι_updateRound2_Л_round2 ,
		 
 		@existT _ _ _  LocalState_ι_updateRounds_Л_round0 ,
 		@existT _ _ _  LocalState_ι_updateRounds_Л_round1 ,
		 @existT _ _ _  LocalState_ι_updateRounds_Л_round2 ,
		 
 		@existT _ _ _  LocalState_ι_withdrawStakeInPoolingRound_Л_participant ,
 		@existT _ _ _  LocalState_ι_withdrawStakeInPoolingRound_Л_round ,
 		@existT _ _ _  LocalState_ι_withdrawStakeInPoolingRound_Л_sv ,
		@existT _ _ _  LocalState_ι_withdrawStakeInPoolingRound_Л_targetAmount ,

		@existT _ _ _  LocalState_ι_constructor5_Л_ok ,

		@existT _ _ _  LocalState_ι__returnOrReinvestForParticipant_Л_round2 ,
		@existT _ _ _  LocalState_ι__returnOrReinvestForParticipant_Л_lostFunds ,
		@existT _ _ _  LocalState_ι__returnOrReinvestForParticipant_Л_params ,

		@existT _ _ _  LocalState_ι_totalParticipantFunds_Л_stakes  ,
		@existT _ _ _  LocalState_ι_totalParticipantFunds_Л_pair ,

		@existT _ _ _  LocalState_ι_updateRounds_Л_roundPre0 ,
		@existT _ _ _  LocalState_ι_cutDePoolReward_Л_reward ,
		@existT _ _ _  LocalState_ι_onBounce_Л_optRound ,

		@existT _ _ _  LocalState_ι_startRoundCompleting_Л_round ,
		@existT _ _ _  LocalState_ι_cutWithdrawalValue_Л_withdrawalTons ,
		@existT _ _ _  LocalState_ι_cutWithdrawalValue_Л_tonsForOwner ,
		@existT _ _ _  LocalState_ι_constructor6_Л_proxy

 	  ]   ;  
 	 ctor := LocalStateC 
} .             

Global Instance Acc_LocalState_ι__addStakes_Л_participant  : Accessor LocalState_ι__addStakes_Л_participant :=  {  acc := ·0  }   . 
Global Instance Acc_LocalState_ι__addStakes_Л_round   : Accessor LocalState_ι__addStakes_Л_round :=  {  acc := ·1  }   . 
Global Instance Acc_LocalState_ι__addStakes_Л_sv  : Accessor LocalState_ι__addStakes_Л_sv :=  {  acc := ·2  }   . 

Global Instance Acc_LocalState_ι__returnOrReinvestForParticipant_Л_attachedValue  : Accessor LocalState_ι__returnOrReinvestForParticipant_Л_attachedValue :=  {  acc := ·3  }   .  
Global Instance Acc_LocalState_ι__returnOrReinvestForParticipant_Л_newLock  : Accessor LocalState_ι__returnOrReinvestForParticipant_Л_newLock :=  {  acc := ·4  }   . 
Global Instance Acc_LocalState_ι__returnOrReinvestForParticipant_Л_newStake  : Accessor LocalState_ι__returnOrReinvestForParticipant_Л_newStake :=  {  acc := ·5  }   . 
Global Instance Acc_LocalState_ι__returnOrReinvestForParticipant_Л_newVesting   : Accessor LocalState_ι__returnOrReinvestForParticipant_Л_newVesting :=  {  acc := ·6  }   . 
Global Instance Acc_LocalState_ι__returnOrReinvestForParticipant_Л_participant  : Accessor LocalState_ι__returnOrReinvestForParticipant_Л_participant :=  {  acc := ·7  }   . 
Global Instance Acc_LocalState_ι__returnOrReinvestForParticipant_Л_reward  : Accessor LocalState_ι__returnOrReinvestForParticipant_Л_reward :=  {  acc := ·8  }   . 
Global Instance Acc_LocalState_ι__returnOrReinvestForParticipant_Л_round0  : Accessor LocalState_ι__returnOrReinvestForParticipant_Л_round0 :=  {  acc := ·9  }   . 

(* Global Instance Acc_LocalState_ι__returnOrReinvest_Л_chunkSize  : Accessor LocalState_ι__returnOrReinvest_Л_chunkSize :=  {  acc := ·10  }   .  *)
Global Instance Acc_LocalState_ι__returnOrReinvest_Л_round2  : Accessor LocalState_ι__returnOrReinvest_Л_round2 :=  {  acc := ·10  }   . 
Global Instance Acc_LocalState_ι__returnOrReinvest_Л_round0   : Accessor LocalState_ι__returnOrReinvest_Л_round0 :=  {  acc := ·11  }   . 
Global Instance Acc_LocalState_ι__returnOrReinvest_Л_startIndex  : Accessor LocalState_ι__returnOrReinvest_Л_startIndex :=  {  acc := ·12  }   . 

Global Instance Acc_LocalState_ι_addVestingOrLock_Л_participant  : Accessor LocalState_ι_addVestingOrLock_Л_participant :=  {  acc := ·13  }   . 
Global Instance Acc_LocalState_ι_addVestingOrLock_Л_l  : Accessor LocalState_ι_addVestingOrLock_Л_l :=  {  acc := ·14  }   . 
Global Instance Acc_LocalState_ι_addVestingOrLock_Л_v  : Accessor LocalState_ι_addVestingOrLock_Л_v :=  {  acc := ·15  }   . 

Global Instance Acc_LocalState_ι_completeRound_Л_i  : Accessor LocalState_ι_completeRound_Л_i :=  {  acc := ·16  }   . 
Global Instance Acc_LocalState_ι_completeRound_Л_msgQty  : Accessor LocalState_ι_completeRound_Л_msgQty :=  {  acc := ·17  }   . 
Global Instance Acc_LocalState_ι_completeRound_Л_restParticipant   : Accessor LocalState_ι_completeRound_Л_restParticipant :=  {  acc := ·18  }   . 

Global Instance Acc_LocalState_ι_cutWithdrawalValue_Л_p  : Accessor LocalState_ι_cutWithdrawalValue_Л_p :=  {  acc := ·19  }   . 
Global Instance Acc_LocalState_ι_cutWithdrawalValue_Л_withdrawal  : Accessor LocalState_ι_cutWithdrawalValue_Л_withdrawal :=  {  acc := ·20  }   . 

Global Instance Acc_LocalState_ι_getRounds_Л_pair  : Accessor LocalState_ι_getRounds_Л_pair :=  {  acc := ·21  }   . 
Global Instance Acc_LocalState_ι_getRounds_Л_rounds  : Accessor LocalState_ι_getRounds_Л_rounds :=  {  acc := ·22  }   .

Global Instance Acc_LocalState_ι_onFailToRecoverStake_Л_round  : Accessor LocalState_ι_onFailToRecoverStake_Л_round :=  {  acc := ·23  }   . 
Global Instance Acc_LocalState_ι_onSuccessToRecoverStake_Л_round  : Accessor LocalState_ι_onSuccessToRecoverStake_Л_round :=  {  acc := ·24  }   . 
Global Instance Acc_LocalState_ι_terminator_Л_round1  : Accessor LocalState_ι_terminator_Л_round1 :=  {  acc := ·25  }   . 

Global Instance Acc_LocalState_ι_transferStakeInOneRound_Л_deltaDestinationStake  : Accessor LocalState_ι_transferStakeInOneRound_Л_deltaDestinationStake :=  {  acc := ·26  }   . 
Global Instance Acc_LocalState_ι_transferStakeInOneRound_Л_destinationParticipant  : Accessor LocalState_ι_transferStakeInOneRound_Л_destinationParticipant :=  {  acc := ·27 }   . 
Global Instance Acc_LocalState_ι_transferStakeInOneRound_Л_newSourceStake  : Accessor LocalState_ι_transferStakeInOneRound_Л_newSourceStake :=  {  acc := ·28  }   . 
Global Instance Acc_LocalState_ι_transferStakeInOneRound_Л_round  : Accessor LocalState_ι_transferStakeInOneRound_Л_round :=  {  acc := ·29  }   . 
Global Instance Acc_LocalState_ι_transferStakeInOneRound_Л_sourceParticipant  : Accessor LocalState_ι_transferStakeInOneRound_Л_sourceParticipant :=  {  acc := ·30  }   . 
Global Instance Acc_LocalState_ι_transferStakeInOneRound_Л_sourceStake  : Accessor LocalState_ι_transferStakeInOneRound_Л_sourceStake :=  {  acc := ·31  }   . 

Global Instance Acc_LocalState_ι_transferStake_Л_amount  : Accessor LocalState_ι_transferStake_Л_amount :=  {  acc := ·32  }   . 
Global Instance Acc_LocalState_ι_transferStake_Л_destParticipant  : Accessor LocalState_ι_transferStake_Л_destParticipant :=  {  acc := ·33  }   . 
Global Instance Acc_LocalState_ι_transferStake_Л_pair   : Accessor LocalState_ι_transferStake_Л_pair :=  {  acc := ·34  }   . 
Global Instance Acc_LocalState_ι_transferStake_Л_rounds  : Accessor LocalState_ι_transferStake_Л_rounds :=  {  acc := ·35  }   . 
Global Instance Acc_LocalState_ι_transferStake_Л_srcParticipant  : Accessor LocalState_ι_transferStake_Л_srcParticipant :=  {  acc := ·36  }   . 
Global Instance Acc_LocalState_ι_transferStake_Л_totalSrcStake  : Accessor LocalState_ι_transferStake_Л_totalSrcStake :=  {  acc := ·37  }   . 
Global Instance Acc_LocalState_ι_transferStake_Л_transferred  : Accessor LocalState_ι_transferStake_Л_transferred :=  {  acc := ·38  }   .

Global Instance Acc_LocalState_ι_updateRound2_Л_round2  : Accessor LocalState_ι_updateRound2_Л_round2 :=  {  acc := ·39  }   . 
Global Instance Acc_LocalState_ι_updateRounds_Л_round0  : Accessor LocalState_ι_updateRounds_Л_round0 :=  {  acc := ·40  }   . 
Global Instance Acc_LocalState_ι_updateRounds_Л_round1  : Accessor LocalState_ι_updateRounds_Л_round1 :=  {  acc := ·41  }   . 
Global Instance Acc_LocalState_ι_updateRounds_Л_round2  : Accessor LocalState_ι_updateRounds_Л_round2 :=  {  acc := ·42  }   . 

Global Instance Acc_LocalState_ι_withdrawStakeInPoolingRound_Л_participant  : Accessor LocalState_ι_withdrawStakeInPoolingRound_Л_participant :=  {  acc := ·43  }   . 
Global Instance Acc_LocalState_ι_withdrawStakeInPoolingRound_Л_round  : Accessor LocalState_ι_withdrawStakeInPoolingRound_Л_round :=  {  acc := ·44  }   . 
Global Instance Acc_LocalState_ι_withdrawStakeInPoolingRound_Л_sv  : Accessor LocalState_ι_withdrawStakeInPoolingRound_Л_sv :=  {  acc := ·45  }   . 
Global Instance Acc_LocalState_ι_withdrawStakeInPoolingRound_Л_targetAmount  : Accessor LocalState_ι_withdrawStakeInPoolingRound_Л_targetAmount := {  acc := ·46  } .

Global Instance Acc_LocalState_ι_constructor5_Л_ok  : Accessor LocalState_ι_constructor5_Л_ok := {  acc := ·47  } .
Global Instance Acc_LocalState_ι__returnOrReinvestForParticipant_Л_round2 : Accessor LocalState_ι__returnOrReinvestForParticipant_Л_round2 := {  acc := ·48 } .
Global Instance Acc_LocalState_ι__returnOrReinvestForParticipant_Л_lostFunds : Accessor LocalState_ι__returnOrReinvestForParticipant_Л_lostFunds := {  acc := ·49 } .
Global Instance Acc_LocalState_ι__returnOrReinvestForParticipant_Л_params : Accessor LocalState_ι__returnOrReinvestForParticipant_Л_params := {  acc := ·50 } .

Global Instance Acc_LocalState_ι_totalParticipantFunds_Л_stakes : Accessor LocalState_ι_totalParticipantFunds_Л_stakes := {  acc := ·51 } .
Global Instance Acc_LocalState_ι_totalParticipantFunds_Л_pair : Accessor LocalState_ι_totalParticipantFunds_Л_pair := {  acc := ·52 } .

Global Instance Acc_LocalState_ι_updateRounds_Л_roundPre0 : Accessor LocalState_ι_updateRounds_Л_roundPre0 := {  acc := ·53 } .
Global Instance Acc_LocalState_ι_cutDePoolReward_Л_reward : Accessor LocalState_ι_cutDePoolReward_Л_reward := {  acc := ·54 } .

Global Instance Acc_LocalState_ι_onBounce_Л_optRound : Accessor LocalState_ι_onBounce_Л_optRound := {  acc := ·55 } .

Global Instance Acc_LocalState_ι_startRoundCompleting_Л_round : Accessor LocalState_ι_startRoundCompleting_Л_round := {  acc := ·56 } .
Global Instance Acc_LocalState_ι_cutWithdrawalValue_Л_withdrawalTons : Accessor LocalState_ι_cutWithdrawalValue_Л_withdrawalTons := {  acc := ·57 } .
Global Instance Acc_LocalState_ι_cutWithdrawalValue_Л_tonsForOwner : Accessor LocalState_ι_cutWithdrawalValue_Л_tonsForOwner := {  acc := ·58 } .
Global Instance Acc_LocalState_ι_constructor6_Л_proxy : Accessor LocalState_ι_constructor6_Л_proxy := {  acc := ·59 } .



Instance LocalState_default : XDefault LocalState :=  {  
	  default := LocalStateC 	default default default default default default default default default default
                            default default default default default default default default default default
                            default default default default default default default default default default
                            default default default default default default default default default default
                            default default default default default default default default default default
							              default default default default default default default default default default
} .
