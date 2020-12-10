Load "Some_more_tools.v".
 Record library_ErrorsP { I }  := library_ErrorsC  { 
 	library_Errors_ι_IS_NOT_OWNER : I  ;   (*constant := 100*) 
 	library_Errors_ι_NOT_ENOUGH_FUNDS : I  ;   (*constant := 105*) 
 	library_Errors_ι_IS_NOT_OWNER2 : I  ;   (*constant := 106*) 
 	library_Errors_ι_IS_NOT_ELECTOR : I  ;   (*constant := 107*) 
 	library_Errors_ι_IS_EXT_MSG : I  ;   (*constant := 108*) 
 	library_Errors_ι_INVALID_ELECTOR_CONFIRM : I  ;   (*constant := 110*) 
 	library_Errors_ι_INVALID_ELECTION_ID : I  ;   (*constant := 111*) 
 	library_Errors_ι_REPEATED_REQUEST : I  ;   (*constant := 112*) 
 	library_Errors_ι_IS_NOT_NODE : I  ;   (*constant := 113*) 
 	library_Errors_ι_DEPOOL_IS_CLOSED : I  ;   (*constant := 114*) 
 	library_Errors_ι_NO_SUCH_STAKEHOLDER : I  ;   (*constant := 116*) 
 	library_Errors_ι_WRONG_ROUND_STATE : I  ;   (*constant := 118*) 
 	library_Errors_ι_INVALID_ADDRESS : I  ;   (*constant := 119*) 
 	library_Errors_ι_IS_NOT_DEPOOL : I  ;   (*constant := 120*) 
 	library_Errors_ι_NO_PENDING_ROUNDS : I  ;   (*constant := 121*) 
 	library_Errors_ι_PENDING_ROUND_IS_TOO_YOUNG : I  ;   (*constant := 122*) 
 }   . 
 
 Arguments library_ErrorsC  [  I  ]   . 
    Record OwnerBase_ι_OwnerP  { A I64 }  := OwnerBase_ι_OwnerC  { 
 	OwnerBase_ι_Owner_ι_addr : A  ;  
 	OwnerBase_ι_Owner_ι_reward : I64   
  }  .  
 
 
 Arguments OwnerBase_ι_OwnerC  [  A I64  ]   . 
 Record OwnerBaseP { A I64 }  := OwnerBaseC  { 
 	OwnerBase_ι_m_owner : (@ OwnerBase_ι_OwnerP A I64 ) 
 
 } . 
 
 Arguments OwnerBaseC  [ A I64 ] 
   . 
 Record ElectorBase_ι_RequestP  { I64 I256 I32 I8 }  := ElectorBase_ι_RequestC  { 
 	ElectorBase_ι_Request_ι_queryId : I64  ;  
 	ElectorBase_ι_Request_ι_validatorKey : I256  ;  
 	ElectorBase_ι_Request_ι_stakeAt : I32  ;  
 	ElectorBase_ι_Request_ι_maxFactor : I32  ;  
 	ElectorBase_ι_Request_ι_adnlAddr : I256  ;  
 	ElectorBase_ι_Request_ι_signature : I8   
  }  .  
 
 
 Arguments ElectorBase_ι_RequestC  [  I64 I256 I32 I8  ]   . 
 Record ElectorBaseP { I64 A }  := ElectorBaseC  { 
 	ElectorBase_ι_RECOVER_STAKE_MSG_VALUE : I64  ;   (*constant := 1e9*) 
 	ElectorBase_ι_m_elector : A  
 
 }   . 
 
 Arguments ElectorBaseC  [  I64 A  ]   . 
 Record ElectionParams_ι_ValidatorDescr73P  { I8 I32 I256 I64 }  := ElectionParams_ι_ValidatorDescr73C  { 
 	ElectionParams_ι_ValidatorDescr73_ι_validator_addr73 : I8  ;  
 	ElectionParams_ι_ValidatorDescr73_ι_ed25519_pubkey : I32  ;  
 	ElectionParams_ι_ValidatorDescr73_ι_pubkey : I256  ;  
 	ElectionParams_ι_ValidatorDescr73_ι_weight : I64  ;  
 	ElectionParams_ι_ValidatorDescr73_ι_adnl_addr : I256   
  }  .  
 
 
 Arguments ElectionParams_ι_ValidatorDescr73C  [  I8 I32 I256 I64  ]   . 
 Record ElectionParamsP { I32 }  := ElectionParamsC  { 
 	ElectionParams_ι_m_electAt : I32  ; 
 	ElectionParams_ι_m_beginBefore : I32  ; 
 	ElectionParams_ι_m_endBefore : I32  ; 
 	ElectionParams_ι_m_electedFor : I32  ; 
 	ElectionParams_ι_m_heldFor : I32  
 
 }   . 
 
 Arguments ElectionParamsC  [  I32  ]   . 
 Record StakeholderBase_ι_StakeholderP  { I64 B I32 A }  := StakeholderBase_ι_StakeholderC  { 
 	StakeholderBase_ι_Stakeholder_ι_totalStake : I64  ;  
 	StakeholderBase_ι_Stakeholder_ι_unusedStake : I64  ;  
 	StakeholderBase_ι_Stakeholder_ι_reinvest : B  ;  
 	StakeholderBase_ι_Stakeholder_ι_reward : I64  ;  
 	StakeholderBase_ι_Stakeholder_ι_lastPaymentUnixTime : I64  ;  
 	StakeholderBase_ι_Stakeholder_ι_withdrawalPeriod : I32  ;  
 	StakeholderBase_ι_Stakeholder_ι_periodPayment : I64  ;  
 	StakeholderBase_ι_Stakeholder_ι_vestingOwner : A   
  }  .  
 
 
 Arguments StakeholderBase_ι_StakeholderC  [  I64 B I32 A  ]   . 
 Record StakeholderBaseP { HM : Type -> Type -> Type } { I64 B I32 A }  := StakeholderBaseC  { 
 	StakeholderBase_ι_m_stakeholders : HM A (@ StakeholderBase_ι_StakeholderP I64 B I32 A ) 
 } . 
 
 Arguments StakeholderBaseC [ HM I64 B I32 A ] 
   . 
 Record StakingOwner_ι_AddressP  { A }  := StakingOwner_ι_AddressC  { 
 	StakingOwner_ι_Address_ι_addr : A   
  }  .  
 
 
 Arguments StakingOwner_ι_AddressC  [  A  ]   . 
 Record StakingOwnerP { I A }  := StakingOwnerC  { 
 	StakingOwner_ι_TICKTOCK_FEE : I  ;   (*constant := 1e9*) 
 	StakingOwner_ι_TIMER_FEE : I  ;   (*constant := 1e9*) 
 	StakingOwner_ι_m_stakingPool : A  ; 
 
 	StakingOwner_ι_m_timer : A  ; 
 	StakingOwner_ι_m_timeout : I  
 
 }   . 
 
 Arguments StakingOwnerC  [  I A  ]   . 
 Record StakingProxyContractP { I64 A }  := StakingProxyContractC  { 
 	StakingProxyContract_ι_PROXY_FEE : I64  ;   (*constant := 1e7*) 
 	StakingProxyContract_ι_m_staking : A  ; 
 	StakingProxyContract_ι_m_elector : A  
 
 }   . 
 
 Arguments StakingProxyContractC  [  I64 A  ]   . 
 Record RoundsBase_ι_StakeValueP  { I64 }  := RoundsBase_ι_StakeValueC  { 
 	RoundsBase_ι_StakeValue_ι_simple : I64  ;  
 	RoundsBase_ι_StakeValue_ι_vesting : I64   
  }  .  
 
 
 Arguments RoundsBase_ι_StakeValueC  [  I64  ]   . 
 Record RoundsBase_ι_RoundP { HM : Type -> Type -> Type } { I32 I8 I64 A }  := RoundsBase_ι_RoundC  { 
 	RoundsBase_ι_Round_ι_id : I32  ;  
 	RoundsBase_ι_Round_ι_step : I8  ;  
 	RoundsBase_ι_Round_ι_participantQty : I32  ;  
 	RoundsBase_ι_Round_ι_stake : I64  ;  
 	RoundsBase_ι_Round_ι_rewards : I64  ;  
 	RoundsBase_ι_Round_ι_unused : I64  ;  
 	RoundsBase_ι_Round_ι_completionStatus : I8  ;  
 	RoundsBase_ι_Round_ι_start : I32  ;  
 	RoundsBase_ι_Round_ι_end : I32  ;  
 	RoundsBase_ι_Round_ι_stakes : HM A (@ RoundsBase_ι_StakeValueP I64 )   
  }  .  
 
 
 Arguments RoundsBase_ι_RoundC [ HM I32 I8 I64 A ]   . 
 Record RoundsBase_ι_RoundInfoP  { I32 I8 I64 }  := RoundsBase_ι_RoundInfoC  { 
 	RoundsBase_ι_RoundInfo_ι_id : I32  ;  
 	RoundsBase_ι_RoundInfo_ι_start : I32  ;  
 	RoundsBase_ι_RoundInfo_ι_end : I32  ;  
 	RoundsBase_ι_RoundInfo_ι_step : I8  ;  
 	RoundsBase_ι_RoundInfo_ι_completionStatus : I8  ;  
 	RoundsBase_ι_RoundInfo_ι_stake : I64  ;  
 	RoundsBase_ι_RoundInfo_ι_stakeholderCount : I32  ;  
 	RoundsBase_ι_RoundInfo_ι_rewards : I64   
  }  .  
 
 
 Arguments RoundsBase_ι_RoundInfoC  [  I32 I8 I64  ]   . 
 Record RoundsBaseP { HM : Type -> Type -> Type } { I8 I64 I32 A }  := RoundsBaseC  { 
 	RoundsBase_ι_STEP_POOLING : I8 ; (*constant := 0*) 
 	RoundsBase_ι_STEP_WAITING_REQUESTS : I8 ; (*constant := 1*) 
 	RoundsBase_ι_STEP_ELECTIONS : I8 ; (*constant := 2*) 
 	RoundsBase_ι_STEP_WAITING_ELECTION_RESULTS : I8 ; (*constant := 3*) 
 	RoundsBase_ι_STEP_WAITING_UNFREEZE : I8 ; (*constant := 4*) 
 	RoundsBase_ι_STEP_COMPLETED : I8 ; (*constant := 5*) 
 	RoundsBase_ι_STEP_COMPLETING : I8 ; (*constant := 6*) 
 	RoundsBase_ι_ROUND_UNDEFINED : I8 ; (*constant := 0*) 
 	RoundsBase_ι_ROUND_RECEIVED_REWARD : I8 ; (*constant := 7*) 
 	RoundsBase_ι_ROUND_POOL_CLOSED : I8 ; (*constant := 1*) 
 	RoundsBase_ι_ROUND_MISSED_ELECTIONS : I8 ; (*constant := 2*) 
 	RoundsBase_ι_ROUND_NOT_ENOUGH_TOTAL_STAKE : I8 ; (*constant := 3*) 
 	RoundsBase_ι_ROUND_NODE_STAKE_TOO_SMALL : I8 ; (*constant := 4*) 
 	RoundsBase_ι_ROUND_STAKE_REJECTED : I8 ; (*constant := 5*) 
 	RoundsBase_ι_ROUND_LOST_ELECTIONS : I8 ; (*constant := 6*) 
 	RoundsBase_ι_m_rounds : HM I64 (@ RoundsBase_ι_RoundP HM I32 I8 I64 A ) ; 
 	RoundsBase_ι_m_startIdx : I64 ; 
 	RoundsBase_ι_m_roundsCount : I8 ; 
 	RoundsBase_ι_m_pendingRounds : HM I32 (@ RoundsBase_ι_RoundP HM I32 I8 I64 A ) 
 } . 
 
 Arguments RoundsBaseC [ HM I8 I64 I32 A ] 
   . 
 Record StakingContractP { HM : Type -> Type -> Type } { I I64 I8 B A I256 I32 }  := StakingContractC  { 
 	StakingContract_ι_NOM_FRACTION : I ; (*constant := 70*) 
 	StakingContract_ι_NODE_FRACTION : I ; (*constant := 25*) 
 	StakingContract_ι_REMOVE_STAKE_FEE : I64 ; (*constant := 3e7*) 
 	StakingContract_ι_TRANSFER_STAKE_FEE : I64 ; (*constant := 1e8*) 
 	StakingContract_ι_ADD_STAKE_FEE : I64 ; (*constant := 3e8*) 
 	StakingContract_ι_PAUSE_STAKE_FEE : I64 ; (*constant := 3e7*) 
 	StakingContract_ι_SET_REINVEST_FEE : I64 ; (*constant := 3e7*) 
 	StakingContract_ι_NOTIFY_FEE : I64 ; (*constant := 3e6*) 
 	StakingContract_ι_MIN_VAL_STAKE : I ; (*constant := 10001000000000*) 
 	StakingContract_ι_MAX_MSGS_PER_TR : I8 ; (*constant := 40*) 
 	StakingContract_ι_NODE_WALLET_MIN_STAKE : I8 ; (*constant := 20*) 
 	StakingContract_ι_ROUND_UP_VALUE : I64 ; (*constant := 1e9*) 
 	StakingContract_ι_ANSWER_MSG_FEE : I64 ; (*constant := 3e6*) 
 	StakingContract_ι_MAX_MONEY_VALUE : I64 ; (*constant := 0xFFFF_FFFF_FFFF_FFFF*) 
 	StakingContract_ι_STATUS_SUCCESS : I8 ; (*constant := 0*) 
 	StakingContract_ι_STATUS_STAKE_TOO_SMALL : I8 ; (*constant := 1*) 
 	StakingContract_ι_STATUS_NO_ACTIVE_ROUNDS : I8 ; (*constant := 2*) 
 	StakingContract_ι_STATUS_POOL_CLOSED : I8 ; (*constant := 3*) 
 	StakingContract_ι_STATUS_ROUND_STAKE_LIMIT : I8 ; (*constant := 4*) 
 	StakingContract_ι_STATUS_MSG_VAL_TOO_SMALL : I8 ; (*constant := 5*) 
 	StakingContract_ι_STATUS_NO_STAKEHOLDER : I8 ; (*constant := 6*) 
 	StakingContract_ι_STATUS_NO_TRANSFER_WHILE_PENDING_ROUND : I8 ; (*constant := 8*) 
 	StakingContract_ι_STATUS_STAKEHOLDER_HAVE_ALREADY_VESTING : I8 ; (*constant := 9*) 
 	StakingContract_ι_STATUS_WITHDRAWAL_PERIOD_GREATER_TOTAL_PERIOD : I8 ; (*constant := 10*) 
 	StakingContract_ι_STATUS_TOTAL_PERIOD_MORE_100YEARS : I8 ; (*constant := 11*) 
 	StakingContract_ι_STATUS_WITHDRAWAL_PERIOD_IS_ZERO : I8 ; (*constant := 12*) 
 	StakingContract_ι_STATUS_TOTAL_PERIOD_IS_NOT_DIVED_BY_WITHDRAWAL_PERIOD : I8 ; (*constant := 13*) 
 	StakingContract_ι_STATUS_PERIOD_PAYMENT_IS_ZERO : I8 ; (*constant := 14*) 
 	StakingContract_ι_STATUS_NO_AVAILABLE_TOKENS : I8 ; (*constant := 15*) 
 	StakingContract_ι_m_poolClosed : B ; 
 	StakingContract_ι_m_requests : HM I32 (@ ElectorBase_ι_RequestP I64 I256 I32 I8 ) ; 
 	StakingContract_ι_m_nodeWallet : A ; 
 	StakingContract_ι_m_minStake : I64 ; 
 	StakingContract_ι_m_minRoundStake : I64 ; 
 	StakingContract_ι_m_maxRoundStake : I64 ; 
 	StakingContract_ι_m_lastRoundInterest : I64 
 
 
 
 
 } . 
 
 Arguments StakingContractC [ HM I I64 I8 B A I256 I32 ] 
   . 
 Record DePool_ι_StakeInfoP  { I32 I64 }  := DePool_ι_StakeInfoC  { 
 	DePool_ι_StakeInfo_ι_roundId : I32  ;  
 	DePool_ι_StakeInfo_ι_stake : I64  ;  
 	DePool_ι_StakeInfo_ι_vesting : I64   
  }  .  
 
 
 Arguments DePool_ι_StakeInfoC  [  I32 I64  ]   . 
 Record TestElector_ι_ValidatorP  { I64 I256 I32 I8 }  := TestElector_ι_ValidatorC  { 
 	TestElector_ι_Validator_ι_stake : I64  ;  
 	TestElector_ι_Validator_ι_key : I256  ;  
 	TestElector_ι_Validator_ι_reward : I64  ;  
 	TestElector_ι_Validator_ι_qid : I64  ;  
 	TestElector_ι_Validator_ι_factor : I32  ;  
 	TestElector_ι_Validator_ι_adnl : I256  ;  
 	TestElector_ι_Validator_ι_signature : I8   
  }  .  
 
 
 Arguments TestElector_ι_ValidatorC  [  I64 I256 I32 I8  ]   . 
 Record TestElectorP { HM : Type -> Type -> Type } { I32 I64 I256 I8 }  := TestElectorC  { 
 	TestElector_ι_elections : HM I256 (@ TestElector_ι_ValidatorP I64 I256 I32 I8 ) ; 
 	TestElector_ι_electAt : I32 ; 
 	TestElector_ι_ELECTIONS_BEGIN_BEFORE : I32 ; (*constant := 12*) 
 	TestElector_ι_ELECTIONS_END_BEFORE : I32 ; (*constant := 6*) 
 	TestElector_ι_ELECTED_FOR : I32 ; (*constant := 24*) 
 	TestElector_ι_STAKE_HELD_FOR : I32 ; (*constant := 12*) 
 
 } . 
 
 Arguments TestElectorC [ HM I32 I64 I256 I8 ] 
   . 
 Record LedgerP { HM : Type -> Type -> Type } { I A I64 I32 B I8 I256 }  := LedgerC  { 
 	Ledger_ι_type_library_Errors : (@ library_ErrorsP I )  ; 
 	Ledger_ι_type_Participant : I8  ; 
 	Ledger_ι_type_Stakeholder : I8  ; 
 	Ledger_ι_type_AcceptBase : I8  ; 
 	Ledger_ι_type_OwnerBase : (@ OwnerBaseP A I64 )  ; 
 	Ledger_ι_type_ElectorBase : (@ ElectorBaseP I64 A )  ; 
 	Ledger_ι_type_ElectionParams : (@ ElectionParamsP I32 )  ; 
 	Ledger_ι_type_StakeholderBase : (@ StakeholderBaseP HM I64 B I32 A )  ; 
 	Ledger_ι_type_StakingOwner : (@ StakingOwnerP I A )  ; 
 	Ledger_ι_type_StakingProxyContract : (@ StakingProxyContractP I64 A )  ; 
 	Ledger_ι_type_RoundsBase : (@ RoundsBaseP HM I8 I64 I32 A )  ; 
 	Ledger_ι_type_StakingContract : (@ StakingContractP HM I I64 I8 B A I256 I32 )  ; 
 	Ledger_ι_type_DePool : I8  ; 
 	Ledger_ι_type_TestElector : (@ TestElectorP HM I32 I64 I256 I8 )  
 }   . 
 
 Arguments LedgerC [ HM I A I64 I32 B I8 I256 ] . 
 
Module LedgerClass (xt: XTypesSig) (sm: StateMonadSig) .
Module SolidityNotations := SolidityNotations.SolidityNotations xt sm.
Import SolidityNotations.
Existing Instance monadStateT.
Existing Instance monadStateStateT.
  
  
 Definition library_Errors := @library_ErrorsP XInteger . 
Global Instance Struct_library_Errors : Struct library_Errors :=  { 
 	fields :=  [ 
 		@existT _ _ _ library_Errors_ι_IS_NOT_OWNER , 
 		@existT _ _ _ library_Errors_ι_NOT_ENOUGH_FUNDS , 
 		@existT _ _ _ library_Errors_ι_IS_NOT_OWNER2 , 
 		@existT _ _ _ library_Errors_ι_IS_NOT_ELECTOR , 
 		@existT _ _ _ library_Errors_ι_IS_EXT_MSG , 
 		@existT _ _ _ library_Errors_ι_INVALID_ELECTOR_CONFIRM , 
 		@existT _ _ _ library_Errors_ι_INVALID_ELECTION_ID , 
 		@existT _ _ _ library_Errors_ι_REPEATED_REQUEST , 
 		@existT _ _ _ library_Errors_ι_IS_NOT_NODE , 
 		@existT _ _ _ library_Errors_ι_DEPOOL_IS_CLOSED , 
 		@existT _ _ _ library_Errors_ι_NO_SUCH_STAKEHOLDER , 
 		@existT _ _ _ library_Errors_ι_WRONG_ROUND_STATE , 
 		@existT _ _ _ library_Errors_ι_INVALID_ADDRESS , 
 		@existT _ _ _ library_Errors_ι_IS_NOT_DEPOOL , 
 		@existT _ _ _ library_Errors_ι_NO_PENDING_ROUNDS , 
 		@existT _ _ _ library_Errors_ι_PENDING_ROUND_IS_TOO_YOUNG 
 	 ]   ;  
 	 ctor := @library_ErrorsC XInteger 
 }   . 
Global Instance Acc_library_Errors_ι_IS_NOT_OWNER : Accessor library_Errors_ι_IS_NOT_OWNER :=  {  acc := ·0  }   . 
Global Instance Acc_library_Errors_ι_NOT_ENOUGH_FUNDS : Accessor library_Errors_ι_NOT_ENOUGH_FUNDS :=  {  acc := ·1  }   . 
Global Instance Acc_library_Errors_ι_IS_NOT_OWNER2 : Accessor library_Errors_ι_IS_NOT_OWNER2 :=  {  acc := ·2  }   . 
Global Instance Acc_library_Errors_ι_IS_NOT_ELECTOR : Accessor library_Errors_ι_IS_NOT_ELECTOR :=  {  acc := ·3  }   . 
Global Instance Acc_library_Errors_ι_IS_EXT_MSG : Accessor library_Errors_ι_IS_EXT_MSG :=  {  acc := ·4  }   . 
Global Instance Acc_library_Errors_ι_INVALID_ELECTOR_CONFIRM : Accessor library_Errors_ι_INVALID_ELECTOR_CONFIRM :=  {  acc := ·5  }   . 
Global Instance Acc_library_Errors_ι_INVALID_ELECTION_ID : Accessor library_Errors_ι_INVALID_ELECTION_ID :=  {  acc := ·6  }   . 
Global Instance Acc_library_Errors_ι_REPEATED_REQUEST : Accessor library_Errors_ι_REPEATED_REQUEST :=  {  acc := ·7  }   . 
Global Instance Acc_library_Errors_ι_IS_NOT_NODE : Accessor library_Errors_ι_IS_NOT_NODE :=  {  acc := ·8  }   . 
Global Instance Acc_library_Errors_ι_DEPOOL_IS_CLOSED : Accessor library_Errors_ι_DEPOOL_IS_CLOSED :=  {  acc := ·9  }   . 
Global Instance Acc_library_Errors_ι_NO_SUCH_STAKEHOLDER : Accessor library_Errors_ι_NO_SUCH_STAKEHOLDER :=  {  acc := ·10  }   . 
Global Instance Acc_library_Errors_ι_WRONG_ROUND_STATE : Accessor library_Errors_ι_WRONG_ROUND_STATE :=  {  acc := ·11  }   . 
Global Instance Acc_library_Errors_ι_INVALID_ADDRESS : Accessor library_Errors_ι_INVALID_ADDRESS :=  {  acc := ·12  }   . 
Global Instance Acc_library_Errors_ι_IS_NOT_DEPOOL : Accessor library_Errors_ι_IS_NOT_DEPOOL :=  {  acc := ·13  }   . 
Global Instance Acc_library_Errors_ι_NO_PENDING_ROUNDS : Accessor library_Errors_ι_NO_PENDING_ROUNDS :=  {  acc := ·14  }   . 
Global Instance Acc_library_Errors_ι_PENDING_ROUND_IS_TOO_YOUNG : Accessor library_Errors_ι_PENDING_ROUND_IS_TOO_YOUNG :=  {  acc := ·15  }   . 
Instance library_Errors_default : XDefault library_Errors :=  {  
 	 default := library_ErrorsC default default default default default default default default default default default default default default default default  
  }   . 
(* Definition library_ErrorsT := StateT library_Errors . *) 
    
  
 Definition OwnerBase_ι_Owner := @OwnerBase_ι_OwnerP XAddress XInteger64 . 
 Definition OwnerBase := @OwnerBaseP  XAddress XInteger64 . 
 Bind Scope struct_scope with OwnerBase_ι_Owner  . 
Global Instance Struct_OwnerBase_ι_Owner : Struct OwnerBase_ι_Owner :=  {  
 	 fields :=  [  
 		@existT _ _ _ OwnerBase_ι_Owner_ι_addr , 
 		@existT _ _ _ OwnerBase_ι_Owner_ι_reward 
 	  ]   ;  
 	 ctor := @OwnerBase_ι_OwnerC XAddress XInteger64 
 }   . 
Global Instance Acc_OwnerBase_ι_Owner_ι_addr : Accessor OwnerBase_ι_Owner_ι_addr :=  {  acc := ·0  }   . 
Global Instance Acc_OwnerBase_ι_Owner_ι_reward : Accessor OwnerBase_ι_Owner_ι_reward :=  {  acc := ·1  }   . 
Global Instance Struct_OwnerBase : Struct OwnerBase :=  { 
 	fields :=  [ 
 		@existT _ _ _ OwnerBase_ι_m_owner 
 
 	 ]   ;  
 	 ctor := @OwnerBaseC  XAddress XInteger64 
 }   . 
Global Instance Acc_OwnerBase_ι_m_owner : Accessor OwnerBase_ι_m_owner :=  {  acc := ·0  }   . 
Instance OwnerBase_ι_Owner_default : XDefault OwnerBase_ι_Owner :=  {  
 	 default := OwnerBase_ι_OwnerC default default  
  }   . 
Instance OwnerBase_default : XDefault OwnerBase :=  {  
 	 default := OwnerBaseC default  
  }   . 
(* Definition OwnerBaseT := StateT OwnerBase . *) 
 
  
 Definition ElectorBase_ι_Request := @ElectorBase_ι_RequestP XInteger64 XInteger256 XInteger32 XInteger8 . 
 Definition ElectorBase := @ElectorBaseP XInteger64 XAddress . 
 Bind Scope struct_scope with ElectorBase_ι_Request  . 
Global Instance Struct_ElectorBase_ι_Request : Struct ElectorBase_ι_Request :=  {  
 	 fields :=  [  
 		@existT _ _ _ ElectorBase_ι_Request_ι_queryId , 
 		@existT _ _ _ ElectorBase_ι_Request_ι_validatorKey , 
 		@existT _ _ _ ElectorBase_ι_Request_ι_stakeAt , 
 		@existT _ _ _ ElectorBase_ι_Request_ι_maxFactor , 
 		@existT _ _ _ ElectorBase_ι_Request_ι_adnlAddr , 
 		@existT _ _ _ ElectorBase_ι_Request_ι_signature 
 	  ]   ;  
 	 ctor := @ElectorBase_ι_RequestC XInteger64 XInteger256 XInteger32 XInteger8 
 }   . 
Global Instance Acc_ElectorBase_ι_Request_ι_queryId : Accessor ElectorBase_ι_Request_ι_queryId :=  {  acc := ·0  }   . 
Global Instance Acc_ElectorBase_ι_Request_ι_validatorKey : Accessor ElectorBase_ι_Request_ι_validatorKey :=  {  acc := ·1  }   . 
Global Instance Acc_ElectorBase_ι_Request_ι_stakeAt : Accessor ElectorBase_ι_Request_ι_stakeAt :=  {  acc := ·2  }   . 
Global Instance Acc_ElectorBase_ι_Request_ι_maxFactor : Accessor ElectorBase_ι_Request_ι_maxFactor :=  {  acc := ·3  }   . 
Global Instance Acc_ElectorBase_ι_Request_ι_adnlAddr : Accessor ElectorBase_ι_Request_ι_adnlAddr :=  {  acc := ·4  }   . 
Global Instance Acc_ElectorBase_ι_Request_ι_signature : Accessor ElectorBase_ι_Request_ι_signature :=  {  acc := ·5  }   . 
Global Instance Struct_ElectorBase : Struct ElectorBase :=  { 
 	fields :=  [ 
 		@existT _ _ _ ElectorBase_ι_RECOVER_STAKE_MSG_VALUE , 
 		@existT _ _ _ ElectorBase_ι_m_elector 
 
 	 ]   ;  
 	 ctor := @ElectorBaseC XInteger64 XAddress 
 }   . 
Global Instance Acc_ElectorBase_ι_RECOVER_STAKE_MSG_VALUE : Accessor ElectorBase_ι_RECOVER_STAKE_MSG_VALUE :=  {  acc := ·0  }   . 
Global Instance Acc_ElectorBase_ι_m_elector : Accessor ElectorBase_ι_m_elector :=  {  acc := ·1  }   . 
Instance ElectorBase_ι_Request_default : XDefault ElectorBase_ι_Request :=  {  
 	 default := ElectorBase_ι_RequestC default default default default default default  
  }   . 
Instance ElectorBase_default : XDefault ElectorBase :=  {  
 	 default := ElectorBaseC default default  
  }   . 
(* Definition ElectorBaseT := StateT ElectorBase . *) 
 
  
 Definition ElectionParams_ι_ValidatorDescr73 := @ElectionParams_ι_ValidatorDescr73P XInteger8 XInteger32 XInteger256 XInteger64 . 
 Definition ElectionParams := @ElectionParamsP XInteger32 . 
 Bind Scope struct_scope with ElectionParams_ι_ValidatorDescr73  . 
Global Instance Struct_ElectionParams_ι_ValidatorDescr73 : Struct ElectionParams_ι_ValidatorDescr73 :=  {  
 	 fields :=  [  
 		@existT _ _ _ ElectionParams_ι_ValidatorDescr73_ι_validator_addr73 , 
 		@existT _ _ _ ElectionParams_ι_ValidatorDescr73_ι_ed25519_pubkey , 
 		@existT _ _ _ ElectionParams_ι_ValidatorDescr73_ι_pubkey , 
 		@existT _ _ _ ElectionParams_ι_ValidatorDescr73_ι_weight , 
 		@existT _ _ _ ElectionParams_ι_ValidatorDescr73_ι_adnl_addr 
 	  ]   ;  
 	 ctor := @ElectionParams_ι_ValidatorDescr73C XInteger8 XInteger32 XInteger256 XInteger64 
 }   . 
Global Instance Acc_ElectionParams_ι_ValidatorDescr73_ι_validator_addr73 : Accessor ElectionParams_ι_ValidatorDescr73_ι_validator_addr73 :=  {  acc := ·0  }   . 
Global Instance Acc_ElectionParams_ι_ValidatorDescr73_ι_ed25519_pubkey : Accessor ElectionParams_ι_ValidatorDescr73_ι_ed25519_pubkey :=  {  acc := ·1  }   . 
Global Instance Acc_ElectionParams_ι_ValidatorDescr73_ι_pubkey : Accessor ElectionParams_ι_ValidatorDescr73_ι_pubkey :=  {  acc := ·2  }   . 
Global Instance Acc_ElectionParams_ι_ValidatorDescr73_ι_weight : Accessor ElectionParams_ι_ValidatorDescr73_ι_weight :=  {  acc := ·3  }   . 
Global Instance Acc_ElectionParams_ι_ValidatorDescr73_ι_adnl_addr : Accessor ElectionParams_ι_ValidatorDescr73_ι_adnl_addr :=  {  acc := ·4  }   . 
Global Instance Struct_ElectionParams : Struct ElectionParams :=  { 
 	fields :=  [ 
 		@existT _ _ _ ElectionParams_ι_m_electAt , 
 		@existT _ _ _ ElectionParams_ι_m_beginBefore , 
 		@existT _ _ _ ElectionParams_ι_m_endBefore , 
 		@existT _ _ _ ElectionParams_ι_m_electedFor , 
 		@existT _ _ _ ElectionParams_ι_m_heldFor 
 
 	 ]   ;  
 	 ctor := @ElectionParamsC XInteger32 
 }   . 
Global Instance Acc_ElectionParams_ι_m_electAt : Accessor ElectionParams_ι_m_electAt :=  {  acc := ·0  }   . 
Global Instance Acc_ElectionParams_ι_m_beginBefore : Accessor ElectionParams_ι_m_beginBefore :=  {  acc := ·1  }   . 
Global Instance Acc_ElectionParams_ι_m_endBefore : Accessor ElectionParams_ι_m_endBefore :=  {  acc := ·2  }   . 
Global Instance Acc_ElectionParams_ι_m_electedFor : Accessor ElectionParams_ι_m_electedFor :=  {  acc := ·3  }   . 
Global Instance Acc_ElectionParams_ι_m_heldFor : Accessor ElectionParams_ι_m_heldFor :=  {  acc := ·4  }   . 
Instance ElectionParams_ι_ValidatorDescr73_default : XDefault ElectionParams_ι_ValidatorDescr73 :=  {  
 	 default := ElectionParams_ι_ValidatorDescr73C default default default default default  
  }   . 
Instance ElectionParams_default : XDefault ElectionParams :=  {  
 	 default := ElectionParamsC default default default default default  
  }   . 
(* Definition ElectionParamsT := StateT ElectionParams . *) 
 
  
 Definition StakeholderBase_ι_Stakeholder := @StakeholderBase_ι_StakeholderP XInteger64 XBool XInteger32 XAddress . 
 Definition StakeholderBase := @StakeholderBaseP XHMap XInteger64 XBool XInteger32 XAddress . 
 Bind Scope struct_scope with StakeholderBase_ι_Stakeholder  . 
Global Instance Struct_StakeholderBase_ι_Stakeholder : Struct StakeholderBase_ι_Stakeholder :=  {  
 	 fields :=  [  
 		@existT _ _ _ StakeholderBase_ι_Stakeholder_ι_totalStake , 
 		@existT _ _ _ StakeholderBase_ι_Stakeholder_ι_unusedStake , 
 		@existT _ _ _ StakeholderBase_ι_Stakeholder_ι_reinvest , 
 		@existT _ _ _ StakeholderBase_ι_Stakeholder_ι_reward , 
 		@existT _ _ _ StakeholderBase_ι_Stakeholder_ι_lastPaymentUnixTime , 
 		@existT _ _ _ StakeholderBase_ι_Stakeholder_ι_withdrawalPeriod , 
 		@existT _ _ _ StakeholderBase_ι_Stakeholder_ι_periodPayment , 
 		@existT _ _ _ StakeholderBase_ι_Stakeholder_ι_vestingOwner 
 	  ]   ;  
 	 ctor := @StakeholderBase_ι_StakeholderC XInteger64 XBool XInteger32 XAddress 
 }   . 
Global Instance Acc_StakeholderBase_ι_Stakeholder_ι_totalStake : Accessor StakeholderBase_ι_Stakeholder_ι_totalStake :=  {  acc := ·0  }   . 
Global Instance Acc_StakeholderBase_ι_Stakeholder_ι_unusedStake : Accessor StakeholderBase_ι_Stakeholder_ι_unusedStake :=  {  acc := ·1  }   . 
Global Instance Acc_StakeholderBase_ι_Stakeholder_ι_reinvest : Accessor StakeholderBase_ι_Stakeholder_ι_reinvest :=  {  acc := ·2  }   . 
Global Instance Acc_StakeholderBase_ι_Stakeholder_ι_reward : Accessor StakeholderBase_ι_Stakeholder_ι_reward :=  {  acc := ·3  }   . 
Global Instance Acc_StakeholderBase_ι_Stakeholder_ι_lastPaymentUnixTime : Accessor StakeholderBase_ι_Stakeholder_ι_lastPaymentUnixTime :=  {  acc := ·4  }   . 
Global Instance Acc_StakeholderBase_ι_Stakeholder_ι_withdrawalPeriod : Accessor StakeholderBase_ι_Stakeholder_ι_withdrawalPeriod :=  {  acc := ·5  }   . 
Global Instance Acc_StakeholderBase_ι_Stakeholder_ι_periodPayment : Accessor StakeholderBase_ι_Stakeholder_ι_periodPayment :=  {  acc := ·6  }   . 
Global Instance Acc_StakeholderBase_ι_Stakeholder_ι_vestingOwner : Accessor StakeholderBase_ι_Stakeholder_ι_vestingOwner :=  {  acc := ·7  }   . 
Global Instance Struct_StakeholderBase : Struct StakeholderBase :=  { 
 	fields :=  [ 
 		@existT _ _ _ StakeholderBase_ι_m_stakeholders 
 	 ]   ;  
 	 ctor := @StakeholderBaseC XHMap XInteger64 XBool XInteger32 XAddress 
 }   . 
Global Instance Acc_StakeholderBase_ι_m_stakeholders : Accessor StakeholderBase_ι_m_stakeholders :=  {  acc := ·0  }   . 
Instance StakeholderBase_ι_Stakeholder_default : XDefault StakeholderBase_ι_Stakeholder :=  {  
 	 default := StakeholderBase_ι_StakeholderC default default default default default default default default  
  }   . 
Instance StakeholderBase_default : XDefault StakeholderBase :=  {  
 	 default := StakeholderBaseC default  
  }   . 
(* Definition StakeholderBaseT := StateT StakeholderBase . *) 
 
  
 Definition StakingOwner_ι_Address := @StakingOwner_ι_AddressP XAddress . 
 Definition StakingOwner := @StakingOwnerP XInteger XAddress . 
 Bind Scope struct_scope with StakingOwner_ι_Address  . 
Global Instance Struct_StakingOwner_ι_Address : Struct StakingOwner_ι_Address :=  {  
 	 fields :=  [  
 		@existT _ _ _ StakingOwner_ι_Address_ι_addr 
 	  ]   ;  
 	 ctor := @StakingOwner_ι_AddressC XAddress 
 }   . 
Global Instance Acc_StakingOwner_ι_Address_ι_addr : Accessor StakingOwner_ι_Address_ι_addr :=  {  acc := ·0  }   . 
Global Instance Struct_StakingOwner : Struct StakingOwner :=  { 
 	fields :=  [ 
 		@existT _ _ _ StakingOwner_ι_TICKTOCK_FEE , 
 		@existT _ _ _ StakingOwner_ι_TIMER_FEE , 
 		@existT _ _ _ StakingOwner_ι_m_stakingPool , 
 
 		@existT _ _ _ StakingOwner_ι_m_timer , 
 		@existT _ _ _ StakingOwner_ι_m_timeout 
 
 	 ]   ;  
 	 ctor := @StakingOwnerC XInteger XAddress 
 }   . 
Global Instance Acc_StakingOwner_ι_TICKTOCK_FEE : Accessor StakingOwner_ι_TICKTOCK_FEE :=  {  acc := ·0  }   . 
Global Instance Acc_StakingOwner_ι_TIMER_FEE : Accessor StakingOwner_ι_TIMER_FEE :=  {  acc := ·1  }   . 
Global Instance Acc_StakingOwner_ι_m_stakingPool : Accessor StakingOwner_ι_m_stakingPool :=  {  acc := ·2  }   . 
Global Instance Acc_StakingOwner_ι_m_timer : Accessor StakingOwner_ι_m_timer :=  {  acc := ·3  }   . 
Global Instance Acc_StakingOwner_ι_m_timeout : Accessor StakingOwner_ι_m_timeout :=  {  acc := ·4  }   . 
Instance StakingOwner_ι_Address_default : XDefault StakingOwner_ι_Address :=  {  
 	 default := StakingOwner_ι_AddressC default  
  }   . 
Instance StakingOwner_default : XDefault StakingOwner :=  {  
 	 default := StakingOwnerC default default default default default  
  }   . 
(* Definition StakingOwnerT := StateT StakingOwner . *) 
 
  
 Definition StakingProxyContract := @StakingProxyContractP XInteger64 XAddress . 
Global Instance Struct_StakingProxyContract : Struct StakingProxyContract :=  { 
 	fields :=  [ 
 		@existT _ _ _ StakingProxyContract_ι_PROXY_FEE , 
 		@existT _ _ _ StakingProxyContract_ι_m_staking , 
 		@existT _ _ _ StakingProxyContract_ι_m_elector 
 
 	 ]   ;  
 	 ctor := @StakingProxyContractC XInteger64 XAddress 
 }   . 
Global Instance Acc_StakingProxyContract_ι_PROXY_FEE : Accessor StakingProxyContract_ι_PROXY_FEE :=  {  acc := ·0  }   . 
Global Instance Acc_StakingProxyContract_ι_m_staking : Accessor StakingProxyContract_ι_m_staking :=  {  acc := ·1  }   . 
Global Instance Acc_StakingProxyContract_ι_m_elector : Accessor StakingProxyContract_ι_m_elector :=  {  acc := ·2  }   . 
Instance StakingProxyContract_default : XDefault StakingProxyContract :=  {  
 	 default := StakingProxyContractC default default default  
  }   . 
(* Definition StakingProxyContractT := StateT StakingProxyContract . *) 
 
  
 Definition RoundsBase_ι_StakeValue := @RoundsBase_ι_StakeValueP XInteger64 . 
 Definition RoundsBase_ι_Round := @RoundsBase_ι_RoundP XHMap XInteger32 XInteger8 XInteger64 XAddress . 
 Definition RoundsBase_ι_RoundInfo := @RoundsBase_ι_RoundInfoP XInteger32 XInteger8 XInteger64 . 
 Definition RoundsBase := @RoundsBaseP XHMap XInteger8 XInteger64 XInteger32 XAddress . 
 Bind Scope struct_scope with RoundsBase_ι_StakeValue  . 
 Bind Scope struct_scope with RoundsBase_ι_Round  . 
 Bind Scope struct_scope with RoundsBase_ι_RoundInfo  . 
Global Instance Struct_RoundsBase_ι_StakeValue : Struct RoundsBase_ι_StakeValue :=  {  
 	 fields :=  [  
 		@existT _ _ _ RoundsBase_ι_StakeValue_ι_simple , 
 		@existT _ _ _ RoundsBase_ι_StakeValue_ι_vesting 
 	  ]   ;  
 	 ctor := @RoundsBase_ι_StakeValueC XInteger64 
 }   . 
Global Instance Acc_RoundsBase_ι_StakeValue_ι_simple : Accessor RoundsBase_ι_StakeValue_ι_simple :=  {  acc := ·0  }   . 
Global Instance Acc_RoundsBase_ι_StakeValue_ι_vesting : Accessor RoundsBase_ι_StakeValue_ι_vesting :=  {  acc := ·1  }   . 
Global Instance Struct_RoundsBase_ι_Round : Struct RoundsBase_ι_Round :=  {  
 	 fields :=  [  
 		@existT _ _ _ RoundsBase_ι_Round_ι_id , 
 		@existT _ _ _ RoundsBase_ι_Round_ι_step , 
 		@existT _ _ _ RoundsBase_ι_Round_ι_participantQty , 
 		@existT _ _ _ RoundsBase_ι_Round_ι_stake , 
 		@existT _ _ _ RoundsBase_ι_Round_ι_rewards , 
 		@existT _ _ _ RoundsBase_ι_Round_ι_unused , 
 		@existT _ _ _ RoundsBase_ι_Round_ι_completionStatus , 
 		@existT _ _ _ RoundsBase_ι_Round_ι_start , 
 		@existT _ _ _ RoundsBase_ι_Round_ι_end , 
 		@existT _ _ _ RoundsBase_ι_Round_ι_stakes 
 	  ]   ;  
 	 ctor := @RoundsBase_ι_RoundC XHMap XInteger32 XInteger8 XInteger64 XAddress 
 }   . 
Global Instance Acc_RoundsBase_ι_Round_ι_id : Accessor RoundsBase_ι_Round_ι_id :=  {  acc := ·0  }   . 
Global Instance Acc_RoundsBase_ι_Round_ι_step : Accessor RoundsBase_ι_Round_ι_step :=  {  acc := ·1  }   . 
Global Instance Acc_RoundsBase_ι_Round_ι_participantQty : Accessor RoundsBase_ι_Round_ι_participantQty :=  {  acc := ·2  }   . 
Global Instance Acc_RoundsBase_ι_Round_ι_stake : Accessor RoundsBase_ι_Round_ι_stake :=  {  acc := ·3  }   . 
Global Instance Acc_RoundsBase_ι_Round_ι_rewards : Accessor RoundsBase_ι_Round_ι_rewards :=  {  acc := ·4  }   . 
Global Instance Acc_RoundsBase_ι_Round_ι_unused : Accessor RoundsBase_ι_Round_ι_unused :=  {  acc := ·5  }   . 
Global Instance Acc_RoundsBase_ι_Round_ι_completionStatus : Accessor RoundsBase_ι_Round_ι_completionStatus :=  {  acc := ·6  }   . 
Global Instance Acc_RoundsBase_ι_Round_ι_start : Accessor RoundsBase_ι_Round_ι_start :=  {  acc := ·7  }   . 
Global Instance Acc_RoundsBase_ι_Round_ι_end : Accessor RoundsBase_ι_Round_ι_end :=  {  acc := ·8  }   . 
Global Instance Acc_RoundsBase_ι_Round_ι_stakes : Accessor RoundsBase_ι_Round_ι_stakes :=  {  acc := ·9  }   . 
Global Instance Struct_RoundsBase_ι_RoundInfo : Struct RoundsBase_ι_RoundInfo :=  {  
 	 fields :=  [  
 		@existT _ _ _ RoundsBase_ι_RoundInfo_ι_id , 
 		@existT _ _ _ RoundsBase_ι_RoundInfo_ι_start , 
 		@existT _ _ _ RoundsBase_ι_RoundInfo_ι_end , 
 		@existT _ _ _ RoundsBase_ι_RoundInfo_ι_step , 
 		@existT _ _ _ RoundsBase_ι_RoundInfo_ι_completionStatus , 
 		@existT _ _ _ RoundsBase_ι_RoundInfo_ι_stake , 
 		@existT _ _ _ RoundsBase_ι_RoundInfo_ι_stakeholderCount , 
 		@existT _ _ _ RoundsBase_ι_RoundInfo_ι_rewards 
 	  ]   ;  
 	 ctor := @RoundsBase_ι_RoundInfoC XInteger32 XInteger8 XInteger64 
 }   . 
Global Instance Acc_RoundsBase_ι_RoundInfo_ι_id : Accessor RoundsBase_ι_RoundInfo_ι_id :=  {  acc := ·0  }   . 
Global Instance Acc_RoundsBase_ι_RoundInfo_ι_start : Accessor RoundsBase_ι_RoundInfo_ι_start :=  {  acc := ·1  }   . 
Global Instance Acc_RoundsBase_ι_RoundInfo_ι_end : Accessor RoundsBase_ι_RoundInfo_ι_end :=  {  acc := ·2  }   . 
Global Instance Acc_RoundsBase_ι_RoundInfo_ι_step : Accessor RoundsBase_ι_RoundInfo_ι_step :=  {  acc := ·3  }   . 
Global Instance Acc_RoundsBase_ι_RoundInfo_ι_completionStatus : Accessor RoundsBase_ι_RoundInfo_ι_completionStatus :=  {  acc := ·4  }   . 
Global Instance Acc_RoundsBase_ι_RoundInfo_ι_stake : Accessor RoundsBase_ι_RoundInfo_ι_stake :=  {  acc := ·5  }   . 
Global Instance Acc_RoundsBase_ι_RoundInfo_ι_stakeholderCount : Accessor RoundsBase_ι_RoundInfo_ι_stakeholderCount :=  {  acc := ·6  }   . 
Global Instance Acc_RoundsBase_ι_RoundInfo_ι_rewards : Accessor RoundsBase_ι_RoundInfo_ι_rewards :=  {  acc := ·7  }   . 
Global Instance Struct_RoundsBase : Struct RoundsBase :=  { 
 	fields :=  [ 
 		@existT _ _ _ RoundsBase_ι_STEP_POOLING , 
 		@existT _ _ _ RoundsBase_ι_STEP_WAITING_REQUESTS , 
 		@existT _ _ _ RoundsBase_ι_STEP_ELECTIONS , 
 		@existT _ _ _ RoundsBase_ι_STEP_WAITING_ELECTION_RESULTS , 
 		@existT _ _ _ RoundsBase_ι_STEP_WAITING_UNFREEZE , 
 		@existT _ _ _ RoundsBase_ι_STEP_COMPLETED , 
 		@existT _ _ _ RoundsBase_ι_STEP_COMPLETING , 
 		@existT _ _ _ RoundsBase_ι_ROUND_UNDEFINED , 
 		@existT _ _ _ RoundsBase_ι_ROUND_RECEIVED_REWARD , 
 		@existT _ _ _ RoundsBase_ι_ROUND_POOL_CLOSED , 
 		@existT _ _ _ RoundsBase_ι_ROUND_MISSED_ELECTIONS , 
 		@existT _ _ _ RoundsBase_ι_ROUND_NOT_ENOUGH_TOTAL_STAKE , 
 		@existT _ _ _ RoundsBase_ι_ROUND_NODE_STAKE_TOO_SMALL , 
 		@existT _ _ _ RoundsBase_ι_ROUND_STAKE_REJECTED , 
 		@existT _ _ _ RoundsBase_ι_ROUND_LOST_ELECTIONS , 
 		@existT _ _ _ RoundsBase_ι_m_rounds , 
 		@existT _ _ _ RoundsBase_ι_m_startIdx , 
 		@existT _ _ _ RoundsBase_ι_m_roundsCount , 
 		@existT _ _ _ RoundsBase_ι_m_pendingRounds 
 	 ]   ;  
 	 ctor := @RoundsBaseC XHMap XInteger8 XInteger64 XInteger32 XAddress 
 }   . 
Global Instance Acc_RoundsBase_ι_STEP_POOLING : Accessor RoundsBase_ι_STEP_POOLING :=  {  acc := ·0  }   . 
Global Instance Acc_RoundsBase_ι_STEP_WAITING_REQUESTS : Accessor RoundsBase_ι_STEP_WAITING_REQUESTS :=  {  acc := ·1  }   . 
Global Instance Acc_RoundsBase_ι_STEP_ELECTIONS : Accessor RoundsBase_ι_STEP_ELECTIONS :=  {  acc := ·2  }   . 
Global Instance Acc_RoundsBase_ι_STEP_WAITING_ELECTION_RESULTS : Accessor RoundsBase_ι_STEP_WAITING_ELECTION_RESULTS :=  {  acc := ·3  }   . 
Global Instance Acc_RoundsBase_ι_STEP_WAITING_UNFREEZE : Accessor RoundsBase_ι_STEP_WAITING_UNFREEZE :=  {  acc := ·4  }   . 
Global Instance Acc_RoundsBase_ι_STEP_COMPLETED : Accessor RoundsBase_ι_STEP_COMPLETED :=  {  acc := ·5  }   . 
Global Instance Acc_RoundsBase_ι_STEP_COMPLETING : Accessor RoundsBase_ι_STEP_COMPLETING :=  {  acc := ·6  }   . 
Global Instance Acc_RoundsBase_ι_ROUND_UNDEFINED : Accessor RoundsBase_ι_ROUND_UNDEFINED :=  {  acc := ·7  }   . 
Global Instance Acc_RoundsBase_ι_ROUND_RECEIVED_REWARD : Accessor RoundsBase_ι_ROUND_RECEIVED_REWARD :=  {  acc := ·8  }   . 
Global Instance Acc_RoundsBase_ι_ROUND_POOL_CLOSED : Accessor RoundsBase_ι_ROUND_POOL_CLOSED :=  {  acc := ·9  }   . 
Global Instance Acc_RoundsBase_ι_ROUND_MISSED_ELECTIONS : Accessor RoundsBase_ι_ROUND_MISSED_ELECTIONS :=  {  acc := ·10  }   . 
Global Instance Acc_RoundsBase_ι_ROUND_NOT_ENOUGH_TOTAL_STAKE : Accessor RoundsBase_ι_ROUND_NOT_ENOUGH_TOTAL_STAKE :=  {  acc := ·11  }   . 
Global Instance Acc_RoundsBase_ι_ROUND_NODE_STAKE_TOO_SMALL : Accessor RoundsBase_ι_ROUND_NODE_STAKE_TOO_SMALL :=  {  acc := ·12  }   . 
Global Instance Acc_RoundsBase_ι_ROUND_STAKE_REJECTED : Accessor RoundsBase_ι_ROUND_STAKE_REJECTED :=  {  acc := ·13  }   . 
Global Instance Acc_RoundsBase_ι_ROUND_LOST_ELECTIONS : Accessor RoundsBase_ι_ROUND_LOST_ELECTIONS :=  {  acc := ·14  }   . 
Global Instance Acc_RoundsBase_ι_m_rounds : Accessor RoundsBase_ι_m_rounds :=  {  acc := ·15  }   . 
Global Instance Acc_RoundsBase_ι_m_startIdx : Accessor RoundsBase_ι_m_startIdx :=  {  acc := ·16  }   . 
Global Instance Acc_RoundsBase_ι_m_roundsCount : Accessor RoundsBase_ι_m_roundsCount :=  {  acc := ·17  }   . 
Global Instance Acc_RoundsBase_ι_m_pendingRounds : Accessor RoundsBase_ι_m_pendingRounds :=  {  acc := ·18  }   . 
Instance RoundsBase_ι_StakeValue_default : XDefault RoundsBase_ι_StakeValue :=  {  
 	 default := RoundsBase_ι_StakeValueC default default  
  }   . 
Instance RoundsBase_ι_Round_default : XDefault RoundsBase_ι_Round :=  {  
 	 default := RoundsBase_ι_RoundC default default default default default default default default default default  
  }   . 
Instance RoundsBase_ι_RoundInfo_default : XDefault RoundsBase_ι_RoundInfo :=  {  
 	 default := RoundsBase_ι_RoundInfoC default default default default default default default default  
  }   . 
Instance RoundsBase_default : XDefault RoundsBase :=  {  
 	 default := RoundsBaseC default default default default default default default default default default default default default default default default default default default  
  }   . 
(* Definition RoundsBaseT := StateT RoundsBase . *) 
 
  
 Definition StakingContract := @StakingContractP XHMap XInteger XInteger64 XInteger8 XBool XAddress XInteger256 XInteger32 . 
Global Instance Struct_StakingContract : Struct StakingContract :=  { 
 	fields :=  [ 
 		@existT _ _ _ StakingContract_ι_NOM_FRACTION , 
 		@existT _ _ _ StakingContract_ι_NODE_FRACTION , 
 		@existT _ _ _ StakingContract_ι_REMOVE_STAKE_FEE , 
 		@existT _ _ _ StakingContract_ι_TRANSFER_STAKE_FEE , 
 		@existT _ _ _ StakingContract_ι_ADD_STAKE_FEE , 
 		@existT _ _ _ StakingContract_ι_PAUSE_STAKE_FEE , 
 		@existT _ _ _ StakingContract_ι_SET_REINVEST_FEE , 
 		@existT _ _ _ StakingContract_ι_NOTIFY_FEE , 
 		@existT _ _ _ StakingContract_ι_MIN_VAL_STAKE , 
 		@existT _ _ _ StakingContract_ι_MAX_MSGS_PER_TR , 
 		@existT _ _ _ StakingContract_ι_NODE_WALLET_MIN_STAKE , 
 		@existT _ _ _ StakingContract_ι_ROUND_UP_VALUE , 
 		@existT _ _ _ StakingContract_ι_ANSWER_MSG_FEE , 
 		@existT _ _ _ StakingContract_ι_MAX_MONEY_VALUE , 
 		@existT _ _ _ StakingContract_ι_STATUS_SUCCESS , 
 		@existT _ _ _ StakingContract_ι_STATUS_STAKE_TOO_SMALL , 
 		@existT _ _ _ StakingContract_ι_STATUS_NO_ACTIVE_ROUNDS , 
 		@existT _ _ _ StakingContract_ι_STATUS_POOL_CLOSED , 
 		@existT _ _ _ StakingContract_ι_STATUS_ROUND_STAKE_LIMIT , 
 		@existT _ _ _ StakingContract_ι_STATUS_MSG_VAL_TOO_SMALL , 
 		@existT _ _ _ StakingContract_ι_STATUS_NO_STAKEHOLDER , 
 		@existT _ _ _ StakingContract_ι_STATUS_NO_TRANSFER_WHILE_PENDING_ROUND , 
 		@existT _ _ _ StakingContract_ι_STATUS_STAKEHOLDER_HAVE_ALREADY_VESTING , 
 		@existT _ _ _ StakingContract_ι_STATUS_WITHDRAWAL_PERIOD_GREATER_TOTAL_PERIOD , 
 		@existT _ _ _ StakingContract_ι_STATUS_TOTAL_PERIOD_MORE_100YEARS , 
 		@existT _ _ _ StakingContract_ι_STATUS_WITHDRAWAL_PERIOD_IS_ZERO , 
 		@existT _ _ _ StakingContract_ι_STATUS_TOTAL_PERIOD_IS_NOT_DIVED_BY_WITHDRAWAL_PERIOD , 
 		@existT _ _ _ StakingContract_ι_STATUS_PERIOD_PAYMENT_IS_ZERO , 
 		@existT _ _ _ StakingContract_ι_STATUS_NO_AVAILABLE_TOKENS , 
 		@existT _ _ _ StakingContract_ι_m_poolClosed , 
 		@existT _ _ _ StakingContract_ι_m_requests , 
 		@existT _ _ _ StakingContract_ι_m_nodeWallet , 
 		@existT _ _ _ StakingContract_ι_m_minStake , 
 		@existT _ _ _ StakingContract_ι_m_minRoundStake , 
 		@existT _ _ _ StakingContract_ι_m_maxRoundStake , 
 		@existT _ _ _ StakingContract_ι_m_lastRoundInterest 
 
 
 
 
 	 ]   ;  
 	 ctor := @StakingContractC XHMap XInteger XInteger64 XInteger8 XBool XAddress XInteger256 XInteger32 
 }   . 
Global Instance Acc_StakingContract_ι_NOM_FRACTION : Accessor StakingContract_ι_NOM_FRACTION :=  {  acc := ·0  }   . 
Global Instance Acc_StakingContract_ι_NODE_FRACTION : Accessor StakingContract_ι_NODE_FRACTION :=  {  acc := ·1  }   . 
Global Instance Acc_StakingContract_ι_REMOVE_STAKE_FEE : Accessor StakingContract_ι_REMOVE_STAKE_FEE :=  {  acc := ·2  }   . 
Global Instance Acc_StakingContract_ι_TRANSFER_STAKE_FEE : Accessor StakingContract_ι_TRANSFER_STAKE_FEE :=  {  acc := ·3  }   . 
Global Instance Acc_StakingContract_ι_ADD_STAKE_FEE : Accessor StakingContract_ι_ADD_STAKE_FEE :=  {  acc := ·4  }   . 
Global Instance Acc_StakingContract_ι_PAUSE_STAKE_FEE : Accessor StakingContract_ι_PAUSE_STAKE_FEE :=  {  acc := ·5  }   . 
Global Instance Acc_StakingContract_ι_SET_REINVEST_FEE : Accessor StakingContract_ι_SET_REINVEST_FEE :=  {  acc := ·6  }   . 
Global Instance Acc_StakingContract_ι_NOTIFY_FEE : Accessor StakingContract_ι_NOTIFY_FEE :=  {  acc := ·7  }   . 
Global Instance Acc_StakingContract_ι_MIN_VAL_STAKE : Accessor StakingContract_ι_MIN_VAL_STAKE :=  {  acc := ·8  }   . 
Global Instance Acc_StakingContract_ι_MAX_MSGS_PER_TR : Accessor StakingContract_ι_MAX_MSGS_PER_TR :=  {  acc := ·9  }   . 
Global Instance Acc_StakingContract_ι_NODE_WALLET_MIN_STAKE : Accessor StakingContract_ι_NODE_WALLET_MIN_STAKE :=  {  acc := ·10  }   . 
Global Instance Acc_StakingContract_ι_ROUND_UP_VALUE : Accessor StakingContract_ι_ROUND_UP_VALUE :=  {  acc := ·11  }   . 
Global Instance Acc_StakingContract_ι_ANSWER_MSG_FEE : Accessor StakingContract_ι_ANSWER_MSG_FEE :=  {  acc := ·12  }   . 
Global Instance Acc_StakingContract_ι_MAX_MONEY_VALUE : Accessor StakingContract_ι_MAX_MONEY_VALUE :=  {  acc := ·13  }   . 
Global Instance Acc_StakingContract_ι_STATUS_SUCCESS : Accessor StakingContract_ι_STATUS_SUCCESS :=  {  acc := ·14  }   . 
Global Instance Acc_StakingContract_ι_STATUS_STAKE_TOO_SMALL : Accessor StakingContract_ι_STATUS_STAKE_TOO_SMALL :=  {  acc := ·15  }   . 
Global Instance Acc_StakingContract_ι_STATUS_NO_ACTIVE_ROUNDS : Accessor StakingContract_ι_STATUS_NO_ACTIVE_ROUNDS :=  {  acc := ·16  }   . 
Global Instance Acc_StakingContract_ι_STATUS_POOL_CLOSED : Accessor StakingContract_ι_STATUS_POOL_CLOSED :=  {  acc := ·17  }   . 
Global Instance Acc_StakingContract_ι_STATUS_ROUND_STAKE_LIMIT : Accessor StakingContract_ι_STATUS_ROUND_STAKE_LIMIT :=  {  acc := ·18  }   . 
Global Instance Acc_StakingContract_ι_STATUS_MSG_VAL_TOO_SMALL : Accessor StakingContract_ι_STATUS_MSG_VAL_TOO_SMALL :=  {  acc := ·19  }   . 
Global Instance Acc_StakingContract_ι_STATUS_NO_STAKEHOLDER : Accessor StakingContract_ι_STATUS_NO_STAKEHOLDER :=  {  acc := ·20  }   . 
Global Instance Acc_StakingContract_ι_STATUS_NO_TRANSFER_WHILE_PENDING_ROUND : Accessor StakingContract_ι_STATUS_NO_TRANSFER_WHILE_PENDING_ROUND :=  {  acc := ·21  }   . 
Global Instance Acc_StakingContract_ι_STATUS_STAKEHOLDER_HAVE_ALREADY_VESTING : Accessor StakingContract_ι_STATUS_STAKEHOLDER_HAVE_ALREADY_VESTING :=  {  acc := ·22  }   . 
Global Instance Acc_StakingContract_ι_STATUS_WITHDRAWAL_PERIOD_GREATER_TOTAL_PERIOD : Accessor StakingContract_ι_STATUS_WITHDRAWAL_PERIOD_GREATER_TOTAL_PERIOD :=  {  acc := ·23  }   . 
Global Instance Acc_StakingContract_ι_STATUS_TOTAL_PERIOD_MORE_100YEARS : Accessor StakingContract_ι_STATUS_TOTAL_PERIOD_MORE_100YEARS :=  {  acc := ·24  }   . 
Global Instance Acc_StakingContract_ι_STATUS_WITHDRAWAL_PERIOD_IS_ZERO : Accessor StakingContract_ι_STATUS_WITHDRAWAL_PERIOD_IS_ZERO :=  {  acc := ·25  }   . 
Global Instance Acc_StakingContract_ι_STATUS_TOTAL_PERIOD_IS_NOT_DIVED_BY_WITHDRAWAL_PERIOD : Accessor StakingContract_ι_STATUS_TOTAL_PERIOD_IS_NOT_DIVED_BY_WITHDRAWAL_PERIOD :=  {  acc := ·26  }   . 
Global Instance Acc_StakingContract_ι_STATUS_PERIOD_PAYMENT_IS_ZERO : Accessor StakingContract_ι_STATUS_PERIOD_PAYMENT_IS_ZERO :=  {  acc := ·27  }   . 
Global Instance Acc_StakingContract_ι_STATUS_NO_AVAILABLE_TOKENS : Accessor StakingContract_ι_STATUS_NO_AVAILABLE_TOKENS :=  {  acc := ·28  }   . 
Global Instance Acc_StakingContract_ι_m_poolClosed : Accessor StakingContract_ι_m_poolClosed :=  {  acc := ·29  }   . 
Global Instance Acc_StakingContract_ι_m_requests : Accessor StakingContract_ι_m_requests :=  {  acc := ·30  }   . 
Global Instance Acc_StakingContract_ι_m_nodeWallet : Accessor StakingContract_ι_m_nodeWallet :=  {  acc := ·31  }   . 
Global Instance Acc_StakingContract_ι_m_minStake : Accessor StakingContract_ι_m_minStake :=  {  acc := ·32  }   . 
Global Instance Acc_StakingContract_ι_m_minRoundStake : Accessor StakingContract_ι_m_minRoundStake :=  {  acc := ·33  }   . 
Global Instance Acc_StakingContract_ι_m_maxRoundStake : Accessor StakingContract_ι_m_maxRoundStake :=  {  acc := ·34  }   . 
Global Instance Acc_StakingContract_ι_m_lastRoundInterest : Accessor StakingContract_ι_m_lastRoundInterest :=  {  acc := ·35  }   . 
Instance StakingContract_default : XDefault StakingContract :=  {  
 	 default := StakingContractC default default default default default default default default default default default default default default default default default default default default default default default default default default default default default default default default default default default default  
  }   . 
(* Definition StakingContractT := StateT StakingContract . *) 
 
  
 Definition DePool_ι_StakeInfo := @DePool_ι_StakeInfoP XInteger32 XInteger64 . 
 Bind Scope struct_scope with DePool_ι_StakeInfo  . 
Global Instance Struct_DePool_ι_StakeInfo : Struct DePool_ι_StakeInfo :=  {  
 	 fields :=  [  
 		@existT _ _ _ DePool_ι_StakeInfo_ι_roundId , 
 		@existT _ _ _ DePool_ι_StakeInfo_ι_stake , 
 		@existT _ _ _ DePool_ι_StakeInfo_ι_vesting 
 	  ]   ;  
 	 ctor := @DePool_ι_StakeInfoC XInteger32 XInteger64 
 }   . 
Global Instance Acc_DePool_ι_StakeInfo_ι_roundId : Accessor DePool_ι_StakeInfo_ι_roundId :=  {  acc := ·0  }   . 
Global Instance Acc_DePool_ι_StakeInfo_ι_stake : Accessor DePool_ι_StakeInfo_ι_stake :=  {  acc := ·1  }   . 
Global Instance Acc_DePool_ι_StakeInfo_ι_vesting : Accessor DePool_ι_StakeInfo_ι_vesting :=  {  acc := ·2  }   . 
Instance DePool_ι_StakeInfo_default : XDefault DePool_ι_StakeInfo :=  {  
 	 default := DePool_ι_StakeInfoC default default default  
  }   . 
(* Definition DePoolT := StateT DePool . *) 
 
  
 Definition TestElector_ι_Validator := @TestElector_ι_ValidatorP XInteger64 XInteger256 XInteger32 XInteger8 . 
 Definition TestElector := @TestElectorP XHMap XInteger32 XInteger64 XInteger256 XInteger8 . 
 Bind Scope struct_scope with TestElector_ι_Validator  . 
Global Instance Struct_TestElector_ι_Validator : Struct TestElector_ι_Validator :=  {  
 	 fields :=  [  
 		@existT _ _ _ TestElector_ι_Validator_ι_stake , 
 		@existT _ _ _ TestElector_ι_Validator_ι_key , 
 		@existT _ _ _ TestElector_ι_Validator_ι_reward , 
 		@existT _ _ _ TestElector_ι_Validator_ι_qid , 
 		@existT _ _ _ TestElector_ι_Validator_ι_factor , 
 		@existT _ _ _ TestElector_ι_Validator_ι_adnl , 
 		@existT _ _ _ TestElector_ι_Validator_ι_signature 
 	  ]   ;  
 	 ctor := @TestElector_ι_ValidatorC XInteger64 XInteger256 XInteger32 XInteger8 
 }   . 
Global Instance Acc_TestElector_ι_Validator_ι_stake : Accessor TestElector_ι_Validator_ι_stake :=  {  acc := ·0  }   . 
Global Instance Acc_TestElector_ι_Validator_ι_key : Accessor TestElector_ι_Validator_ι_key :=  {  acc := ·1  }   . 
Global Instance Acc_TestElector_ι_Validator_ι_reward : Accessor TestElector_ι_Validator_ι_reward :=  {  acc := ·2  }   . 
Global Instance Acc_TestElector_ι_Validator_ι_qid : Accessor TestElector_ι_Validator_ι_qid :=  {  acc := ·3  }   . 
Global Instance Acc_TestElector_ι_Validator_ι_factor : Accessor TestElector_ι_Validator_ι_factor :=  {  acc := ·4  }   . 
Global Instance Acc_TestElector_ι_Validator_ι_adnl : Accessor TestElector_ι_Validator_ι_adnl :=  {  acc := ·5  }   . 
Global Instance Acc_TestElector_ι_Validator_ι_signature : Accessor TestElector_ι_Validator_ι_signature :=  {  acc := ·6  }   . 
Global Instance Struct_TestElector : Struct TestElector :=  { 
 	fields :=  [ 
 		@existT _ _ _ TestElector_ι_elections , 
 		@existT _ _ _ TestElector_ι_electAt , 
 		@existT _ _ _ TestElector_ι_ELECTIONS_BEGIN_BEFORE , 
 		@existT _ _ _ TestElector_ι_ELECTIONS_END_BEFORE , 
 		@existT _ _ _ TestElector_ι_ELECTED_FOR , 
 		@existT _ _ _ TestElector_ι_STAKE_HELD_FOR 
 
 	 ]   ;  
 	 ctor := @TestElectorC XHMap XInteger32 XInteger64 XInteger256 XInteger8 
 }   . 
Global Instance Acc_TestElector_ι_elections : Accessor TestElector_ι_elections :=  {  acc := ·0  }   . 
Global Instance Acc_TestElector_ι_electAt : Accessor TestElector_ι_electAt :=  {  acc := ·1  }   . 
Global Instance Acc_TestElector_ι_ELECTIONS_BEGIN_BEFORE : Accessor TestElector_ι_ELECTIONS_BEGIN_BEFORE :=  {  acc := ·2  }   . 
Global Instance Acc_TestElector_ι_ELECTIONS_END_BEFORE : Accessor TestElector_ι_ELECTIONS_END_BEFORE :=  {  acc := ·3  }   . 
Global Instance Acc_TestElector_ι_ELECTED_FOR : Accessor TestElector_ι_ELECTED_FOR :=  {  acc := ·4  }   . 
Global Instance Acc_TestElector_ι_STAKE_HELD_FOR : Accessor TestElector_ι_STAKE_HELD_FOR :=  {  acc := ·5  }   . 
Instance TestElector_ι_Validator_default : XDefault TestElector_ι_Validator :=  {  
 	 default := TestElector_ι_ValidatorC default default default default default default default  
  }   . 
Instance TestElector_default : XDefault TestElector :=  {  
 	 default := TestElectorC default default default default default default  
  }   . 
(* Definition TestElectorT := StateT TestElector . *) 
 
  
 Definition Ledger := @LedgerP XHMap XInteger  XAddress XInteger64 XInteger32 XBool XInteger8 XInteger256 . 
Global Instance Struct_Ledger : Struct Ledger :=  { 
 	fields :=  [ 
 		@existT _ _ _ Ledger_ι_type_library_Errors , 
 		@existT _ _ _ Ledger_ι_type_Participant , 
 		@existT _ _ _ Ledger_ι_type_Stakeholder , 
 		@existT _ _ _ Ledger_ι_type_AcceptBase , 
 		@existT _ _ _ Ledger_ι_type_OwnerBase , 
 		@existT _ _ _ Ledger_ι_type_ElectorBase , 
 		@existT _ _ _ Ledger_ι_type_ElectionParams , 
 		@existT _ _ _ Ledger_ι_type_StakeholderBase , 
 		@existT _ _ _ Ledger_ι_type_StakingOwner , 
 		@existT _ _ _ Ledger_ι_type_StakingProxyContract , 
 		@existT _ _ _ Ledger_ι_type_RoundsBase , 
 		@existT _ _ _ Ledger_ι_type_StakingContract , 
 		@existT _ _ _ Ledger_ι_type_DePool , 
 		@existT _ _ _ Ledger_ι_type_TestElector 
 	 ]   ;  
 	 ctor := @LedgerC XHMap XInteger  XAddress XInteger64 XInteger32 XBool XInteger8 XInteger256 
 }   . 
Global Instance Acc_Ledger_ι_type_library_Errors : Accessor Ledger_ι_type_library_Errors :=  {  acc := ·0  }   . 
Global Instance Acc_Ledger_ι_type_Participant : Accessor Ledger_ι_type_Participant :=  {  acc := ·1  }   . 
Global Instance Acc_Ledger_ι_type_Stakeholder : Accessor Ledger_ι_type_Stakeholder :=  {  acc := ·2  }   . 
Global Instance Acc_Ledger_ι_type_AcceptBase : Accessor Ledger_ι_type_AcceptBase :=  {  acc := ·3  }   . 
Global Instance Acc_Ledger_ι_type_OwnerBase : Accessor Ledger_ι_type_OwnerBase :=  {  acc := ·4  }   . 
Global Instance Acc_Ledger_ι_type_ElectorBase : Accessor Ledger_ι_type_ElectorBase :=  {  acc := ·5  }   . 
Global Instance Acc_Ledger_ι_type_ElectionParams : Accessor Ledger_ι_type_ElectionParams :=  {  acc := ·6  }   . 
Global Instance Acc_Ledger_ι_type_StakeholderBase : Accessor Ledger_ι_type_StakeholderBase :=  {  acc := ·7  }   . 
Global Instance Acc_Ledger_ι_type_StakingOwner : Accessor Ledger_ι_type_StakingOwner :=  {  acc := ·8  }   . 
Global Instance Acc_Ledger_ι_type_StakingProxyContract : Accessor Ledger_ι_type_StakingProxyContract :=  {  acc := ·9  }   . 
Global Instance Acc_Ledger_ι_type_RoundsBase : Accessor Ledger_ι_type_RoundsBase :=  {  acc := ·10  }   . 
Global Instance Acc_Ledger_ι_type_StakingContract : Accessor Ledger_ι_type_StakingContract :=  {  acc := ·11  }   . 
Global Instance Acc_Ledger_ι_type_DePool : Accessor Ledger_ι_type_DePool :=  {  acc := ·12  }   . 
Global Instance Acc_Ledger_ι_type_TestElector : Accessor Ledger_ι_type_TestElector :=  {  acc := ·13  }   . 
Instance Ledger_default : XDefault Ledger :=  {  
 	 default := LedgerC default default default default default default default default default default default default default default  
  }   . 
(* Definition LedgerT := StateT Ledger . *) 
 

(* 1 *)
(*embeddedType for all Accessors *)
Definition projEmbed_Accessor {U T}{f: T -> U}`{s: Struct T}`{a: @Accessor T U s f}: T -> U := f.
Definition injEmbed_Accessor {U T}{f: T -> U}`{s: Struct T}`{a: @Accessor T U s f} (x: U) (t: T): T :=
{$ t with f := x $}.
 

Section LedgerSec.

  Definition T1 := library_Errors . 
(*  Definition T2 := Participant . 
 Definition T3 := Stakeholder . 
 Definition T4 := AcceptBase .  *)
 Definition  T2 := OwnerBase . 
  Definition  T3 := ElectorBase . 
  Definition  T4 := ElectionParams . 
  Definition  T5 := StakeholderBase . 
  Definition  T6 := StakingOwner . 
  Definition  T7 := StakingProxyContract . 
  Definition  T8 := RoundsBase . 
  Definition  T9 := StakingContract . 
(*  Definition T13 := DePool .  *)
  Definition  T10 := TestElector . 
 
  
 Definition projEmbed_T1 : Ledger -> T1 := projEmbed_Accessor . 
 Definition injEmbed_T1 : T1 -> Ledger -> Ledger := injEmbed_Accessor . 
 
 Lemma projinj_T1 : forall ( t : T1 ) ( s : Ledger ) , 
 projEmbed_T1 ( injEmbed_T1 t s ) = t . 
 Proof.
 intros. compute. auto.
Qed. 
 
 Lemma injproj_T1 : forall ( s : Ledger ) , injEmbed_T1 ( projEmbed_T1 s ) s = s . Proof.
 intros. destruct s. compute. auto.
Qed. 
 Lemma injinj_T1 : forall ( t1 t2 : T1 ) ( s : Ledger ) , 
 injEmbed_T1 t1 ( injEmbed_T1 t2 s) = 
 injEmbed_T1 t1 s . 
 Proof.
 intros. destruct s. compute. auto.
Qed. 
 
 Instance embeddedT1 : EmbeddedType Ledger T1 := 
 {
 projEmbed := projEmbed_T1 ; 
 injEmbed := injEmbed_T1 ; 
 projinj := projinj_T1 ; 
 injproj := injproj_T1 ; 
 injinj  := injinj_T1 ; 
 } . 
 

 Definition projEmbed_T2 : Ledger -> T2 := projEmbed_Accessor . 
 Definition injEmbed_T2 : T2 -> Ledger -> Ledger := injEmbed_Accessor . 
 
 Lemma projinj_T2 : forall ( t : T2 ) ( s : Ledger ) , 
 projEmbed_T2 ( injEmbed_T2 t s ) = t . 
 Proof.
 intros. compute. auto.
Qed. 
 
 Lemma injproj_T2 : forall ( s : Ledger ) , injEmbed_T2 ( projEmbed_T2 s ) s = s . Proof.
 intros. destruct s. compute. auto.
Qed. 
 Lemma injinj_T2 : forall ( t1 t2 : T2 ) ( s : Ledger ) , 
 injEmbed_T2 t1 ( injEmbed_T2 t2 s) = 
 injEmbed_T2 t1 s . 
 Proof.
 intros. destruct s. compute. auto.
Qed. 
 
 Instance embeddedT2 : EmbeddedType Ledger T2 := 
 {
 projEmbed := projEmbed_T2 ; 
 injEmbed := injEmbed_T2 ; 
 projinj := projinj_T2 ; 
 injproj := injproj_T2 ; 
 injinj  := injinj_T2 ; 
 } . 
 
 
 
 Definition projEmbed_T3 : Ledger -> T3 := projEmbed_Accessor . 
 Definition injEmbed_T3 : T3 -> Ledger -> Ledger := injEmbed_Accessor . 
 
 Lemma projinj_T3 : forall ( t : T3 ) ( s : Ledger ) , 
 projEmbed_T3 ( injEmbed_T3 t s ) = t . 
 Proof.
 intros. compute. auto.
Qed. 
 
 Lemma injproj_T3 : forall ( s : Ledger ) , injEmbed_T3 ( projEmbed_T3 s ) s = s . Proof.
 intros. destruct s. compute. auto.
Qed. 
 Lemma injinj_T3 : forall ( t1 t2 : T3 ) ( s : Ledger ) , 
 injEmbed_T3 t1 ( injEmbed_T3 t2 s) = 
 injEmbed_T3 t1 s . 
 Proof.
 intros. destruct s. compute. auto.
Qed. 
 
 Instance embeddedT3 : EmbeddedType Ledger T3 := 
 {
 projEmbed := projEmbed_T3 ; 
 injEmbed := injEmbed_T3 ; 
 projinj := projinj_T3 ; 
 injproj := injproj_T3 ; 
 injinj  := injinj_T3 ; 
 } . 
 
 
 
 Definition projEmbed_T4 : Ledger -> T4 := projEmbed_Accessor . 
 Definition injEmbed_T4 : T4 -> Ledger -> Ledger := injEmbed_Accessor . 
 
 Lemma projinj_T4 : forall ( t : T4 ) ( s : Ledger ) , 
 projEmbed_T4 ( injEmbed_T4 t s ) = t . 
 Proof.
 intros. compute. auto.
Qed. 
 
 Lemma injproj_T4 : forall ( s : Ledger ) , injEmbed_T4 ( projEmbed_T4 s ) s = s . Proof.
 intros. destruct s. compute. auto.
Qed. 
 Lemma injinj_T4 : forall ( t1 t2 : T4 ) ( s : Ledger ) , 
 injEmbed_T4 t1 ( injEmbed_T4 t2 s) = 
 injEmbed_T4 t1 s . 
 Proof.
 intros. destruct s. compute. auto.
Qed. 
 
 Instance embeddedT4 : EmbeddedType Ledger T4 := 
 {
 projEmbed := projEmbed_T4 ; 
 injEmbed := injEmbed_T4 ; 
 projinj := projinj_T4 ; 
 injproj := injproj_T4 ; 
 injinj  := injinj_T4 ; 
 } . 
 
 
 
 Definition projEmbed_T5 : Ledger -> T5 := projEmbed_Accessor . 
 Definition injEmbed_T5 : T5 -> Ledger -> Ledger := injEmbed_Accessor . 
 
 Lemma projinj_T5 : forall ( t : T5 ) ( s : Ledger ) , 
 projEmbed_T5 ( injEmbed_T5 t s ) = t . 
 Proof.
 intros. compute. auto.
Qed. 
 
 Lemma injproj_T5 : forall ( s : Ledger ) , injEmbed_T5 ( projEmbed_T5 s ) s = s . Proof.
 intros. destruct s. compute. auto.
Qed. 
 Lemma injinj_T5 : forall ( t1 t2 : T5 ) ( s : Ledger ) , 
 injEmbed_T5 t1 ( injEmbed_T5 t2 s) = 
 injEmbed_T5 t1 s . 
 Proof.
 intros. destruct s. compute. auto.
Qed. 
 
 Instance embeddedT5 : EmbeddedType Ledger T5 := 
 {
 projEmbed := projEmbed_T5 ; 
 injEmbed := injEmbed_T5 ; 
 projinj := projinj_T5 ; 
 injproj := injproj_T5 ; 
 injinj  := injinj_T5 ; 
 } . 
 
 
 
 Definition projEmbed_T6 : Ledger -> T6 := projEmbed_Accessor . 
 Definition injEmbed_T6 : T6 -> Ledger -> Ledger := injEmbed_Accessor . 
 
 Lemma projinj_T6 : forall ( t : T6 ) ( s : Ledger ) , 
 projEmbed_T6 ( injEmbed_T6 t s ) = t . 
 Proof.
 intros. compute. auto.
Qed. 
 
 Lemma injproj_T6 : forall ( s : Ledger ) , injEmbed_T6 ( projEmbed_T6 s ) s = s . Proof.
 intros. destruct s. compute. auto.
Qed. 
 Lemma injinj_T6 : forall ( t1 t2 : T6 ) ( s : Ledger ) , 
 injEmbed_T6 t1 ( injEmbed_T6 t2 s) = 
 injEmbed_T6 t1 s . 
 Proof.
 intros. destruct s. compute. auto.
Qed. 
 
 Instance embeddedT6 : EmbeddedType Ledger T6 := 
 {
 projEmbed := projEmbed_T6 ; 
 injEmbed := injEmbed_T6 ; 
 projinj := projinj_T6 ; 
 injproj := injproj_T6 ; 
 injinj  := injinj_T6 ; 
 } . 
 
 
 
 Definition projEmbed_T7 : Ledger -> T7 := projEmbed_Accessor . 
 Definition injEmbed_T7 : T7 -> Ledger -> Ledger := injEmbed_Accessor . 
 
 Lemma projinj_T7 : forall ( t : T7 ) ( s : Ledger ) , 
 projEmbed_T7 ( injEmbed_T7 t s ) = t . 
 Proof.
 intros. compute. auto.
Qed. 
 
 Lemma injproj_T7 : forall ( s : Ledger ) , injEmbed_T7 ( projEmbed_T7 s ) s = s . Proof.
 intros. destruct s. compute. auto.
Qed. 
 Lemma injinj_T7 : forall ( t1 t2 : T7 ) ( s : Ledger ) , 
 injEmbed_T7 t1 ( injEmbed_T7 t2 s) = 
 injEmbed_T7 t1 s . 
 Proof.
 intros. destruct s. compute. auto.
Qed. 
 
 Instance embeddedT7 : EmbeddedType Ledger T7 := 
 {
 projEmbed := projEmbed_T7 ; 
 injEmbed := injEmbed_T7 ; 
 projinj := projinj_T7 ; 
 injproj := injproj_T7 ; 
 injinj  := injinj_T7 ; 
 } . 
 
 
 
 Definition projEmbed_T8 : Ledger -> T8 := projEmbed_Accessor . 
 Definition injEmbed_T8 : T8 -> Ledger -> Ledger := injEmbed_Accessor . 
 
 Lemma projinj_T8 : forall ( t : T8 ) ( s : Ledger ) , 
 projEmbed_T8 ( injEmbed_T8 t s ) = t . 
 Proof.
 intros. compute. auto.
Qed. 
 
 Lemma injproj_T8 : forall ( s : Ledger ) , injEmbed_T8 ( projEmbed_T8 s ) s = s . Proof.
 intros. destruct s. compute. auto.
Qed. 
 Lemma injinj_T8 : forall ( t1 t2 : T8 ) ( s : Ledger ) , 
 injEmbed_T8 t1 ( injEmbed_T8 t2 s) = 
 injEmbed_T8 t1 s . 
 Proof.
 intros. destruct s. compute. auto.
Qed. 
 
 Instance embeddedT8 : EmbeddedType Ledger T8 := 
 {
 projEmbed := projEmbed_T8 ; 
 injEmbed := injEmbed_T8 ; 
 projinj := projinj_T8 ; 
 injproj := injproj_T8 ; 
 injinj  := injinj_T8 ; 
 } . 
 
 
 
 Definition projEmbed_T9 : Ledger -> T9 := projEmbed_Accessor . 
 Definition injEmbed_T9 : T9 -> Ledger -> Ledger := injEmbed_Accessor . 
 
 Lemma projinj_T9 : forall ( t : T9 ) ( s : Ledger ) , 
 projEmbed_T9 ( injEmbed_T9 t s ) = t . 
 Proof.
 intros. compute. auto.
Qed. 
 
 Lemma injproj_T9 : forall ( s : Ledger ) , injEmbed_T9 ( projEmbed_T9 s ) s = s . Proof.
 intros. destruct s. compute. auto.
Qed. 
 Lemma injinj_T9 : forall ( t1 t2 : T9 ) ( s : Ledger ) , 
 injEmbed_T9 t1 ( injEmbed_T9 t2 s) = 
 injEmbed_T9 t1 s . 
 Proof.
 intros. destruct s. compute. auto.
Qed. 
 
 Instance embeddedT9 : EmbeddedType Ledger T9 := 
 {
 projEmbed := projEmbed_T9 ; 
 injEmbed := injEmbed_T9 ; 
 projinj := projinj_T9 ; 
 injproj := injproj_T9 ; 
 injinj  := injinj_T9 ; 
 } . 
 
 
 
 Definition projEmbed_T10 : Ledger -> T10 := projEmbed_Accessor . 
 Definition injEmbed_T10 : T10 -> Ledger -> Ledger := injEmbed_Accessor . 
 
 Lemma projinj_T10 : forall ( t : T10 ) ( s : Ledger ) , 
 projEmbed_T10 ( injEmbed_T10 t s ) = t . 
 Proof.
 intros. compute. auto.
Qed. 
 
 Lemma injproj_T10 : forall ( s : Ledger ) , injEmbed_T10 ( projEmbed_T10 s ) s = s . Proof.
 intros. destruct s. compute. auto.
Qed. 
 Lemma injinj_T10 : forall ( t1 t2 : T10 ) ( s : Ledger ) , 
 injEmbed_T10 t1 ( injEmbed_T10 t2 s) = 
 injEmbed_T10 t1 s . 
 Proof.
 intros. destruct s. compute. auto.
Qed. 
 
 Instance embeddedT10 : EmbeddedType Ledger T10 := 
 {
 projEmbed := projEmbed_T10 ; 
 injEmbed := injEmbed_T10 ; 
 projinj := projinj_T10 ; 
 injproj := injproj_T10 ; 
 injinj  := injinj_T10 ; 
 } . 
 
Lemma injcommute_T1_T2: forall  (u:T2) (t:T1)  (s:Ledger), 
      ( injEmbed u ( injEmbed t s ) ) = ( injEmbed t ( injEmbed u s ) ).
Proof.
 intros. compute. auto.
Qed.
  
Instance InjectCommutableStates_T1_T2: 
         @InjectCommutableStates Ledger T1 T2 
            embeddedT1 embeddedT2 
               := 
{
  injcommute := injcommute_T1_T2
}.
Definition embeddedProduct_T1_T2 := 
           @embeddedProduct Ledger T1 T2 
            embeddedT1 embeddedT2
                 InjectCommutableStates_T1_T2.
Existing Instance embeddedProduct_T1_T2.
 
Lemma injcommute_T1xT2_T3: 
               forall ( u : T3 ) ( t : T1 * T2 ) 
                      ( s:Ledger ), 
      ( injEmbed u ( injEmbed t s ) ) = ( injEmbed t ( injEmbed u s ) ).
Proof.
 intros. compute. auto.
Qed.

Instance InjectCommutableStates_T1xT2_T3 : 
@InjectCommutableStates Ledger (  T1 * T2  ) T3 embeddedProduct_T1_T2 embeddedT3 := 
{
  injcommute := injcommute_T1xT2_T3 
}.

Definition embeddedProduct_T1xT2_T3 := 
           @embeddedProduct Ledger (  T1 * T2  ) T3
           embeddedProduct_T1_T2 embeddedT3
           InjectCommutableStates_T1xT2_T3.

Existing Instance embeddedProduct_T1xT2_T3 .

Lemma injcommute_T1xT2xT3_T4: forall 
( u : T4 ) (t : T1 * T2 * T3 ) ( s : Ledger ) , 
      ( injEmbed u ( injEmbed t s ) ) = ( injEmbed t ( injEmbed u s ) ).
Proof.
 intros. compute. auto.
Qed.
 
Instance InjectCommutableStates_T1xT2xT3_T4 : 
@InjectCommutableStates Ledger (  T1 * T2 * T3  ) T4 embeddedProduct_T1xT2_T3 embeddedT4 := 
{
  injcommute := injcommute_T1xT2xT3_T4 
}.

Definition embeddedProduct_T1xT2xT3_T4 := 
           @embeddedProduct Ledger (  T1 * T2 * T3  ) T4
           embeddedProduct_T1xT2_T3 embeddedT4
           InjectCommutableStates_T1xT2xT3_T4.

Existing Instance embeddedProduct_T1xT2xT3_T4 .
 
Instance InjectCommutableStates_T1xT2xT3xT4_T5 : 
@InjectCommutableStates Ledger (  T1 * T2 * T3 * T4  ) T5 embeddedProduct_T1xT2xT3_T4 embeddedT5 := 
{
  injcommute := injcommuteT1xT2xT3xT4_T5 
}.

Definition embeddedProduct_T1xT2xT3xT4_T5 := 
           @embeddedProduct Ledger (  T1 * T2 * T2 * T3  ) T5
           embeddedProduct_T1xT2xT3_T4 embeddedT5
           InjectCommutableStates_T1xT2xT3xT4_T5.

Existing Instance embeddedProduct_T1xT2xT3xT4_T5 .
 
Instance InjectCommutableStates_T1xT2xT3xT4xT5_T6 : 
@InjectCommutableStates Ledger (  T1 * T2 * T2 * T3 * T4  ) T6 embeddedProduct_T1xT2xT3xT4_T5 embeddedT6 := 
{
  injcommute := injcommuteT1xT2xT3xT4xT5_T6 
}.

Definition embeddedProduct_T1xT2xT3xT4xT5_T6 := 
           @embeddedProduct Ledger (  T1 * T2 * T2 * T3 * T4  ) T6
           embeddedProduct_T1xT2xT3xT4_T5 embeddedT6
           InjectCommutableStates_T1xT2xT3xT4xT5_T6.

Existing Instance embeddedProduct_T1xT2xT3xT4xT5_T6 .
 
Instance InjectCommutableStates_T1xT2xT3xT4xT5xT6_T7 : 
@InjectCommutableStates Ledger (  T1 * T2 * T2 * T3 * T4 * T5  ) T7 embeddedProduct_T1xT2xT3xT4xT5_T6 embeddedT7 := 
{
  injcommute := injcommuteT1xT2xT3xT4xT5xT6_T7 
}.

Definition embeddedProduct_T1xT2xT3xT4xT5xT6_T7 := 
           @embeddedProduct Ledger (  T1 * T2 * T2 * T3 * T4 * T5  ) T7
           embeddedProduct_T1xT2xT3xT4xT5_T6 embeddedT7
           InjectCommutableStates_T1xT2xT3xT4xT5xT6_T7.

Existing Instance embeddedProduct_T1xT2xT3xT4xT5xT6_T7 .
 
Instance InjectCommutableStates_T1xT2xT3xT4xT5xT6xT7_T8 : 
@InjectCommutableStates Ledger (  T1 * T2 * T2 * T3 * T4 * T5 * T6  ) T8 embeddedProduct_T1xT2xT3xT4xT5xT6_T7 embeddedT8 := 
{
  injcommute := injcommuteT1xT2xT3xT4xT5xT6xT7_T8 
}.

Definition embeddedProduct_T1xT2xT3xT4xT5xT6xT7_T8 := 
           @embeddedProduct Ledger (  T1 * T2 * T2 * T3 * T4 * T5 * T6  ) T8
           embeddedProduct_T1xT2xT3xT4xT5xT6_T7 embeddedT8
           InjectCommutableStates_T1xT2xT3xT4xT5xT6xT7_T8.

Existing Instance embeddedProduct_T1xT2xT3xT4xT5xT6xT7_T8 .
 
Instance InjectCommutableStates_T1xT2xT3xT4xT5xT6xT7xT8_T9 : 
@InjectCommutableStates Ledger (  T1 * T2 * T2 * T3 * T4 * T5 * T6 * T7  ) T9 embeddedProduct_T1xT2xT3xT4xT5xT6xT7_T8 embeddedT9 := 
{
  injcommute := injcommuteT1xT2xT3xT4xT5xT6xT7xT8_T9 
}.

Definition embeddedProduct_T1xT2xT3xT4xT5xT6xT7xT8_T9 := 
           @embeddedProduct Ledger (  T1 * T2 * T2 * T3 * T4 * T5 * T6 * T7  ) T9
           embeddedProduct_T1xT2xT3xT4xT5xT6xT7_T8 embeddedT9
           InjectCommutableStates_T1xT2xT3xT4xT5xT6xT7xT8_T9.

Existing Instance embeddedProduct_T1xT2xT3xT4xT5xT6xT7xT8_T9 .
 
Instance InjectCommutableStates_T1xT2xT3xT4xT5xT6xT7xT8xT9_T10 : 
@InjectCommutableStates Ledger (  T1 * T2 * T2 * T3 * T4 * T5 * T6 * T7 * T8  ) T10 embeddedProduct_T1xT2xT3xT4xT5xT6xT7xT8_T9 embeddedT10 := 
{
  injcommute := injcommuteT1xT2xT3xT4xT5xT6xT7xT8xT9_T10 
}.

Definition embeddedProduct_T1xT2xT3xT4xT5xT6xT7xT8xT9_T10 := 
           @embeddedProduct Ledger (  T1 * T2 * T2 * T3 * T4 * T5 * T6 * T7 * T8  ) T10
           embeddedProduct_T1xT2xT3xT4xT5xT6xT7xT8_T9 embeddedT10
           InjectCommutableStates_T1xT2xT3xT4xT5xT6xT7xT8xT9_T10.

Existing Instance embeddedProduct_T1xT2xT3xT4xT5xT6xT7xT8xT9_T10 .
 
Instance InjectCommutableStates_T1xT2xT3xT4xT5xT6xT7xT8xT9xT10_T11 : 
@InjectCommutableStates Ledger (  T1 * T2 * T2 * T3 * T4 * T5 * T6 * T7 * T8 * T9  ) T11 embeddedProduct_T1xT2xT3xT4xT5xT6xT7xT8xT9_T10 embeddedT11 := 
{
  injcommute := injcommuteT1xT2xT3xT4xT5xT6xT7xT8xT9xT10_T11 
}.

Definition embeddedProduct_T1xT2xT3xT4xT5xT6xT7xT8xT9xT10_T11 := 
           @embeddedProduct Ledger (  T1 * T2 * T2 * T3 * T4 * T5 * T6 * T7 * T8 * T9  ) T11
           embeddedProduct_T1xT2xT3xT4xT5xT6xT7xT8xT9_T10 embeddedT11
           InjectCommutableStates_T1xT2xT3xT4xT5xT6xT7xT8xT9xT10_T11.

Existing Instance embeddedProduct_T1xT2xT3xT4xT5xT6xT7xT8xT9xT10_T11 .
 
Instance InjectCommutableStates_T1xT2xT3xT4xT5xT6xT7xT8xT9xT10xT11_T12 : 
@InjectCommutableStates Ledger (  T1 * T2 * T2 * T3 * T4 * T5 * T6 * T7 * T8 * T9 * T10  ) T12 embeddedProduct_T1xT2xT3xT4xT5xT6xT7xT8xT9xT10_T11 embeddedT12 := 
{
  injcommute := injcommuteT1xT2xT3xT4xT5xT6xT7xT8xT9xT10xT11_T12 
}.

Definition embeddedProduct_T1xT2xT3xT4xT5xT6xT7xT8xT9xT10xT11_T12 := 
           @embeddedProduct Ledger (  T1 * T2 * T2 * T3 * T4 * T5 * T6 * T7 * T8 * T9 * T10  ) T12
           embeddedProduct_T1xT2xT3xT4xT5xT6xT7xT8xT9xT10_T11 embeddedT12
           InjectCommutableStates_T1xT2xT3xT4xT5xT6xT7xT8xT9xT10xT11_T12.

Existing Instance embeddedProduct_T1xT2xT3xT4xT5xT6xT7xT8xT9xT10xT11_T12 .
 
Instance InjectCommutableStates_T1xT2xT3xT4xT5xT6xT7xT8xT9xT10xT11xT12_T13 : 
@InjectCommutableStates Ledger (  T1 * T2 * T2 * T3 * T4 * T5 * T6 * T7 * T8 * T9 * T10 * T11  ) T13 embeddedProduct_T1xT2xT3xT4xT5xT6xT7xT8xT9xT10xT11_T12 embeddedT13 := 
{
  injcommute := injcommuteT1xT2xT3xT4xT5xT6xT7xT8xT9xT10xT11xT12_T13 
}.

Definition embeddedProduct_T1xT2xT3xT4xT5xT6xT7xT8xT9xT10xT11xT12_T13 := 
           @embeddedProduct Ledger (  T1 * T2 * T2 * T3 * T4 * T5 * T6 * T7 * T8 * T9 * T10 * T11  ) T13
           embeddedProduct_T1xT2xT3xT4xT5xT6xT7xT8xT9xT10xT11_T12 embeddedT13
           InjectCommutableStates_T1xT2xT3xT4xT5xT6xT7xT8xT9xT10xT11xT12_T13.

Existing Instance embeddedProduct_T1xT2xT3xT4xT5xT6xT7xT8xT9xT10xT11xT12_T13 .
 
Instance InjectCommutableStates_T1xT2xT3xT4xT5xT6xT7xT8xT9xT10xT11xT12xT13_T14 : 
@InjectCommutableStates Ledger (  T1 * T2 * T2 * T3 * T4 * T5 * T6 * T7 * T8 * T9 * T10 * T11 * T12  ) T14 embeddedProduct_T1xT2xT3xT4xT5xT6xT7xT8xT9xT10xT11xT12_T13 embeddedT14 := 
{
  injcommute := injcommuteT1xT2xT3xT4xT5xT6xT7xT8xT9xT10xT11xT12xT13_T14 
}.

Definition embeddedProduct_T1xT2xT3xT4xT5xT6xT7xT8xT9xT10xT11xT12xT13_T14 := 
           @embeddedProduct Ledger (  T1 * T2 * T2 * T3 * T4 * T5 * T6 * T7 * T8 * T9 * T10 * T11 * T12  ) T14
           embeddedProduct_T1xT2xT3xT4xT5xT6xT7xT8xT9xT10xT11xT12_T13 embeddedT14
           InjectCommutableStates_T1xT2xT3xT4xT5xT6xT7xT8xT9xT10xT11xT12xT13_T14.

Existing Instance embeddedProduct_T1xT2xT3xT4xT5xT6xT7xT8xT9xT10xT11xT12xT13_T14 .

End LedgerClass .
