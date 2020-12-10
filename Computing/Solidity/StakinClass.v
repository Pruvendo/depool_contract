Load "Some_more_tools.v".
 
    
   
Record OwnerBase_ι_OwnerP  { A I64 }  := OwnerBase_ι_OwnerC  { 
 	OwnerBase_ι_Owner_ι_addr : A  ;   ( *payable* )  
 	OwnerBase_ι_Owner_ι_reward : I64   
  }  .  
 
 Arguments  OwnerBase_ι_OwnerC   [   A I64   ]    . 
Record  OwnerBaseP {  }  := OwnerBaseC  { 
 	OwnerBase_ι_m_owner :   
 
 }   . 
 Arguments OwnerBaseC  [    ]   . 
Module OwnerBaseClass (xt: XTypesSig) (sm: StateMonadSig) .
Module SolidityNotations := SolidityNotations.SolidityNotations xt sm.
Import SolidityNotations. 
  
Definition  OwnerBase_ι_Owner  := @OwnerBase_ι_OwnerP  XAddress XInteger64  . 
Definition  OwnerBase  := @OwnerBaseP    . 
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
 	ctor := @OwnerBaseC 
 }   . 
Global Instance Acc_OwnerBase_ι_m_owner : Accessor OwnerBase_ι_m_owner :=  {  acc := ·0  }   . 
Instance OwnerBase_ι_Owner_default : XDefault OwnerBase_ι_Owner :=  {  
 	 default := OwnerBase_ι_OwnerC default default  
  }   . 
Instance OwnerBase_default : XDefault OwnerBase :=  {  
 	 default := OwnerBaseC default  
  }   . 
End OwnerBaseClass .

 
Record ElectorBase_ι_RequestP  { I64 I256 I32 I8 }  := ElectorBase_ι_RequestC  { 
 	ElectorBase_ι_Request_ι_queryId : I64  ;  
 	ElectorBase_ι_Request_ι_validatorKey : I256  ;  
 	ElectorBase_ι_Request_ι_stakeAt : I32  ;  
 	ElectorBase_ι_Request_ι_maxFactor : I32  ;  
 	ElectorBase_ι_Request_ι_adnlAddr : I256  ;  
 	ElectorBase_ι_Request_ι_signature : I8   
  }  .  
 
 Arguments  ElectorBase_ι_RequestC   [   I64 I256 I32 I8   ]    . 
Record  ElectorBaseP { I64 A }  := ElectorBaseC  { 
 	ElectorBase_ι_RECOVER_STAKE_MSG_VALUE : I64  ;   ( *constant := 1e9* ) 
 	ElectorBase_ι_m_elector : A  ;   ( *payable* ) 
 
 }   . 
 Arguments ElectorBaseC  [  I64 A  ]   . 
Module ElectorBaseClass (xt: XTypesSig) (sm: StateMonadSig) .
Module SolidityNotations := SolidityNotations.SolidityNotations xt sm.
Import SolidityNotations. 
  
Definition  ElectorBase_ι_Request  := @ElectorBase_ι_RequestP  XInteger64 XInteger256 XInteger32 XInteger8  . 
Definition  ElectorBase  := @ElectorBaseP  XInteger64 XAddress  . 
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
End ElectorBaseClass .

 
Record ElectionParams_ι_ValidatorDescr73P  { I8 I32 I256 I64 }  := ElectionParams_ι_ValidatorDescr73C  { 
 	ElectionParams_ι_ValidatorDescr73_ι_validator_addr73 : I8  ;  
 	ElectionParams_ι_ValidatorDescr73_ι_ed25519_pubkey : I32  ;  
 	ElectionParams_ι_ValidatorDescr73_ι_pubkey : I256  ;  
 	ElectionParams_ι_ValidatorDescr73_ι_weight : I64  ;  
 	ElectionParams_ι_ValidatorDescr73_ι_adnl_addr : I256   
  }  .  
 
 Arguments  ElectionParams_ι_ValidatorDescr73C   [   I8 I32 I256 I64   ]    . 
Record  ElectionParamsP { I32 }  := ElectionParamsC  { 
 	ElectionParams_ι_m_electAt : I32  ; 
 	ElectionParams_ι_m_beginBefore : I32  ; 
 	ElectionParams_ι_m_endBefore : I32  ; 
 	ElectionParams_ι_m_electedFor : I32  ; 
 	ElectionParams_ι_m_heldFor : I32  
 
 }   . 
 Arguments ElectionParamsC  [  I32  ]   . 
Module ElectionParamsClass (xt: XTypesSig) (sm: StateMonadSig) .
Module SolidityNotations := SolidityNotations.SolidityNotations xt sm.
Import SolidityNotations. 
  
Definition  ElectionParams_ι_ValidatorDescr73  := @ElectionParams_ι_ValidatorDescr73P  XInteger8 XInteger32 XInteger256 XInteger64  . 
Definition  ElectionParams  := @ElectionParamsP  XInteger32  . 
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
End ElectionParamsClass .

 
Record StakeholderBase_ι_StakeholderP  { I64 B }  := StakeholderBase_ι_StakeholderC  { 
 	StakeholderBase_ι_Stakeholder_ι_totalStake : I64  ;  
 	StakeholderBase_ι_Stakeholder_ι_unusedStake : I64  ;  
 	StakeholderBase_ι_Stakeholder_ι_reinvest : B  ;  
 	StakeholderBase_ι_Stakeholder_ι_reward : I64   
  }  .  
 
 Arguments  StakeholderBase_ι_StakeholderC   [   I64 B   ]    . 
Record  StakeholderBaseP { Arr }  := StakeholderBaseC  { 
 	StakeholderBase_ι_m_stakeholders : Arr A   
 }   . 
 Arguments StakeholderBaseC  [  Arr  ]   . 
Module StakeholderBaseClass (xt: XTypesSig) (sm: StateMonadSig) .
Module SolidityNotations := SolidityNotations.SolidityNotations xt sm.
Import SolidityNotations. 
  
Definition  StakeholderBase_ι_Stakeholder  := @StakeholderBase_ι_StakeholderP  XInteger64 XBool  . 
Definition  StakeholderBase  := @StakeholderBaseP  XArray  . 
Bind Scope struct_scope with StakeholderBase_ι_Stakeholder  . 
Global Instance Struct_StakeholderBase_ι_Stakeholder : Struct StakeholderBase_ι_Stakeholder :=  {  
 	 fields :=  [  
 		@existT _ _ _ StakeholderBase_ι_Stakeholder_ι_totalStake , 
 		@existT _ _ _ StakeholderBase_ι_Stakeholder_ι_unusedStake , 
 		@existT _ _ _ StakeholderBase_ι_Stakeholder_ι_reinvest , 
 		@existT _ _ _ StakeholderBase_ι_Stakeholder_ι_reward 
 	  ]   ;  
 	 ctor := @StakeholderBase_ι_StakeholderC XInteger64 XBool   
  }   . 
Global Instance Acc_StakeholderBase_ι_Stakeholder_ι_totalStake : Accessor StakeholderBase_ι_Stakeholder_ι_totalStake :=  {  acc := ·0  }   . 
Global Instance Acc_StakeholderBase_ι_Stakeholder_ι_unusedStake : Accessor StakeholderBase_ι_Stakeholder_ι_unusedStake :=  {  acc := ·1  }   . 
Global Instance Acc_StakeholderBase_ι_Stakeholder_ι_reinvest : Accessor StakeholderBase_ι_Stakeholder_ι_reinvest :=  {  acc := ·2  }   . 
Global Instance Acc_StakeholderBase_ι_Stakeholder_ι_reward : Accessor StakeholderBase_ι_Stakeholder_ι_reward :=  {  acc := ·3  }   . 
Global Instance Struct_StakeholderBase : Struct StakeholderBase :=  { 
 	fields :=  [ 
 		@existT _ _ _ StakeholderBase_ι_m_stakeholders 
 	 ]   ;  
 	ctor := @StakeholderBaseC XArray
 }   . 
Global Instance Acc_StakeholderBase_ι_m_stakeholders : Accessor StakeholderBase_ι_m_stakeholders :=  {  acc := ·0  }   . 
Instance StakeholderBase_ι_Stakeholder_default : XDefault StakeholderBase_ι_Stakeholder :=  {  
 	 default := StakeholderBase_ι_StakeholderC default default default default  
  }   . 
Instance StakeholderBase_default : XDefault StakeholderBase :=  {  
 	 default := StakeholderBaseC default  
  }   . 
End StakeholderBaseClass .

 
Record RoundsBase_ι_RoundP  { I32 I8 I64 Arr A }  := RoundsBase_ι_RoundC  { 
 	RoundsBase_ι_Round_ι_id : I32  ;  
 	RoundsBase_ι_Round_ι_step : I8  ;  
 	RoundsBase_ι_Round_ι_count : I32  ;  
 	RoundsBase_ι_Round_ι_totalStake : I64  ;  
 	RoundsBase_ι_Round_ι_rewards : I64  ;  
 	RoundsBase_ι_Round_ι_unused : I64  ;  
 	RoundsBase_ι_Round_ι_completionStatus : I8  ;  
 	RoundsBase_ι_Round_ι_start : I32  ;  
 	RoundsBase_ι_Round_ι_end : I32  ;  
 	RoundsBase_ι_Round_ι_stakes : Arr A I64   
  }  .  
 
 Arguments  RoundsBase_ι_RoundC   [   I32 I8 I64 Arr A   ]    . 
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
 
 Arguments  RoundsBase_ι_RoundInfoC   [   I32 I8 I64   ]    . 
Record  RoundsBaseP { I8 Arr I64 }  := RoundsBaseC  { 
 	RoundsBase_ι_STEP_POOLING : I8  ;   ( *constant := 0* ) 
 	RoundsBase_ι_STEP_WAITING_REQUESTS : I8  ;   ( *constant := 1* ) 
 	RoundsBase_ι_STEP_ELECTIONS : I8  ;   ( *constant := 2* ) 
 	RoundsBase_ι_STEP_WAITING_ELECTION_RESULTS : I8  ;   ( *constant := 3* ) 
 	RoundsBase_ι_STEP_WAITING_UNFREEZE : I8  ;   ( *constant := 4* ) 
 	RoundsBase_ι_STEP_COMPLETED : I8  ;   ( *constant := 5* ) 
 	RoundsBase_ι_STEP_COMPLETING : I8  ;   ( *constant := 6* ) 
 	RoundsBase_ι_ROUND_UNDEFINED : I8  ;   ( *constant := 0* ) 
 	RoundsBase_ι_ROUND_RECEIVED_REWARD : I8  ;   ( *constant := 7* ) 
 	RoundsBase_ι_ROUND_POOL_CLOSED : I8  ;   ( *constant := 1* ) 
 	RoundsBase_ι_ROUND_MISSED_ELECTIONS : I8  ;   ( *constant := 2* ) 
 	RoundsBase_ι_ROUND_NOT_ENOUGH_TOTAL_STAKE : I8  ;   ( *constant := 3* ) 
 	RoundsBase_ι_ROUND_NODE_STAKE_TOO_SMALL : I8  ;   ( *constant := 4* ) 
 	RoundsBase_ι_ROUND_STAKE_REJECTED : I8  ;   ( *constant := 5* ) 
 	RoundsBase_ι_ROUND_LOST_ELECTIONS : I8  ;   ( *constant := 6* ) 
 	RoundsBase_ι_m_rounds : Arr I64   ; 
 	RoundsBase_ι_m_startIdx : I64  ; 
 	RoundsBase_ι_m_roundsCount : I8  ; 
 	RoundsBase_ι_m_pendingRounds : Arr I32   
 }   . 
 Arguments RoundsBaseC  [  I8 Arr I64  ]   . 
Module RoundsBaseClass (xt: XTypesSig) (sm: StateMonadSig) .
Module SolidityNotations := SolidityNotations.SolidityNotations xt sm.
Import SolidityNotations. 
  
Definition  RoundsBase_ι_Round  := @RoundsBase_ι_RoundP  XInteger32 XInteger8 XInteger64 XArray XAddress  . 
Definition  RoundsBase_ι_RoundInfo  := @RoundsBase_ι_RoundInfoP  XInteger32 XInteger8 XInteger64  . 
Definition  RoundsBase  := @RoundsBaseP  XInteger8 XArray XInteger64  . 
Bind Scope struct_scope with RoundsBase_ι_Round  . 
Bind Scope struct_scope with RoundsBase_ι_RoundInfo  . 
Global Instance Struct_RoundsBase_ι_Round : Struct RoundsBase_ι_Round :=  {  
 	 fields :=  [  
 		@existT _ _ _ RoundsBase_ι_Round_ι_id , 
 		@existT _ _ _ RoundsBase_ι_Round_ι_step , 
 		@existT _ _ _ RoundsBase_ι_Round_ι_count , 
 		@existT _ _ _ RoundsBase_ι_Round_ι_totalStake , 
 		@existT _ _ _ RoundsBase_ι_Round_ι_rewards , 
 		@existT _ _ _ RoundsBase_ι_Round_ι_unused , 
 		@existT _ _ _ RoundsBase_ι_Round_ι_completionStatus , 
 		@existT _ _ _ RoundsBase_ι_Round_ι_start , 
 		@existT _ _ _ RoundsBase_ι_Round_ι_end , 
 		@existT _ _ _ RoundsBase_ι_Round_ι_stakes 
 	  ]   ;  
 	 ctor := @RoundsBase_ι_RoundC XInteger32 XInteger8 XInteger64 XArray XAddress   
  }   . 
Global Instance Acc_RoundsBase_ι_Round_ι_id : Accessor RoundsBase_ι_Round_ι_id :=  {  acc := ·0  }   . 
Global Instance Acc_RoundsBase_ι_Round_ι_step : Accessor RoundsBase_ι_Round_ι_step :=  {  acc := ·1  }   . 
Global Instance Acc_RoundsBase_ι_Round_ι_count : Accessor RoundsBase_ι_Round_ι_count :=  {  acc := ·2  }   . 
Global Instance Acc_RoundsBase_ι_Round_ι_totalStake : Accessor RoundsBase_ι_Round_ι_totalStake :=  {  acc := ·3  }   . 
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
 	ctor := @RoundsBaseC XInteger8 XArray XInteger64
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
Instance RoundsBase_ι_Round_default : XDefault RoundsBase_ι_Round :=  {  
 	 default := RoundsBase_ι_RoundC default default default default default default default default default default  
  }   . 
Instance RoundsBase_ι_RoundInfo_default : XDefault RoundsBase_ι_RoundInfo :=  {  
 	 default := RoundsBase_ι_RoundInfoC default default default default default default default default  
  }   . 
Instance RoundsBase_default : XDefault RoundsBase :=  {  
 	 default := RoundsBaseC default default default default default default default default default default default default default default default default default default default  
  }   . 
End RoundsBaseClass .

 
Record StakingContract_ι_NodeP  { A I32 }  := StakingContract_ι_NodeC  { 
 	StakingContract_ι_Node_ι_wallet : A  ;  
 	StakingContract_ι_Node_ι_factor : I32   
   }  .  
 
 Arguments  StakingContract_ι_NodeC   [   A I32   ]    . 
Record StakingContract_ι_StakeInfoP  { I32 I64 }  := StakingContract_ι_StakeInfoC  { 
 	StakingContract_ι_StakeInfo_ι_roundId : I32  ;  
 	StakingContract_ι_StakeInfo_ι_stake : I64   
  }  .  
 
 Arguments  StakingContract_ι_StakeInfoC   [   I32 I64   ]    . 
Record  StakingContractP { I I64 I8 B Arr }  := StakingContractC  { 
 	StakingContract_ι_NOM_FRACTION : I  ;   ( *constant := 70* ) 
 	StakingContract_ι_NODE_FRACTION : I  ;   ( *constant := 25* ) 
 	StakingContract_ι_REMOVE_STAKE_FEE : I64  ;   ( *constant := 3e7* ) 
 	StakingContract_ι_ADD_STAKE_FEE : I64  ;   ( *constant := 3e8* ) 
 	StakingContract_ι_PAUSE_STAKE_FEE : I64  ;   ( *constant := 3e7* ) 
 	StakingContract_ι_CONTINUE_STAKE_FEE : I64  ;   ( *constant := 3e7* ) 
 	StakingContract_ι_SET_REINVEST_FEE : I64  ;   ( *constant := 3e7* ) 
 	StakingContract_ι_NOTIFY_FEE : I64  ;   ( *constant := 3e6* ) 
 	StakingContract_ι_MIN_VAL_STAKE : I  ;   ( *constant := 10001000000000* ) 
 	StakingContract_ι_MAX_MSGS_PER_TR : I8  ;   ( *constant := 40* ) 
 	StakingContract_ι_NODE_WALLET_MIN_STAKE : I8  ;   ( *constant := 20* ) 
 	StakingContract_ι_TICKTOCK_PERIOD : I  ;   ( *constant := 30* ) 
 	StakingContract_ι_ROUND_UP_VALUE : I64  ;   ( *constant := 1e9* ) 
 	StakingContract_ι_ANSWER_MSG_FEE : I64  ;   ( *constant := 3e6* ) 
 	StakingContract_ι_STATUS_SUCCESS : I8  ;   ( *constant := 0* ) 
 
 	StakingContract_ι_STATUS_NO_ACTIVE_ROUNDS : I8  ;   ( *constant := 2* ) 
 	StakingContract_ι_STATUS_POOL_CLOSED : I8  ;   ( *constant := 3* ) 
 	StakingContract_ι_STATUS_ROUND_STAKE_LIMIT : I8  ;   ( *constant := 4* ) 
 	StakingContract_ι_STATUS_MSG_VAL_TOO_SMALL : I8  ;   ( *constant := 5* ) 
 	StakingContract_ι_STATUS_NO_STAKE : I8  ;   ( *constant := 6* ) 
 	StakingContract_ι_m_poolClosed : B  ; 
 	StakingContract_ι_m_requests : Arr I32   ; 
 
 	StakingContract_ι_m_minStake : I64  ; 
 	StakingContract_ι_m_minRoundStake : I64  ; 
 	StakingContract_ι_m_maxRoundStake : I64  ; 
 	StakingContract_ι_m_lastRoundInterest : I64  
 
 
 
 }   . 
 Arguments StakingContractC  [  I I64 I8 B Arr  ]   . 
Module StakingContractClass (xt: XTypesSig) (sm: StateMonadSig) .
Module SolidityNotations := SolidityNotations.SolidityNotations xt sm.
Import SolidityNotations. 
  
Definition  StakingContract_ι_Node  := @StakingContract_ι_NodeP  XAddress XInteger32  . 
Definition  StakingContract_ι_StakeInfo  := @StakingContract_ι_StakeInfoP  XInteger32 XInteger64  . 
Definition  StakingContract  := @StakingContractP  XInteger XInteger64 XInteger8 XBool XArray  . 
Bind Scope struct_scope with StakingContract_ι_Node  . 
Bind Scope struct_scope with StakingContract_ι_StakeInfo  . 
Global Instance Struct_StakingContract_ι_Node : Struct StakingContract_ι_Node :=  {  
 	 fields :=  [  
 		@existT _ _ _ StakingContract_ι_Node_ι_wallet , 
 		@existT _ _ _ StakingContract_ι_Node_ι_factor 
 
 	  ]   ;  
 	 ctor := @StakingContract_ι_NodeC XAddress XInteger32   
  }   . 
Global Instance Acc_StakingContract_ι_Node_ι_wallet : Accessor StakingContract_ι_Node_ι_wallet :=  {  acc := ·0  }   . 
Global Instance Acc_StakingContract_ι_Node_ι_factor : Accessor StakingContract_ι_Node_ι_factor :=  {  acc := ·1  }   . 
Global Instance Struct_StakingContract_ι_StakeInfo : Struct StakingContract_ι_StakeInfo :=  {  
 	 fields :=  [  
 		@existT _ _ _ StakingContract_ι_StakeInfo_ι_roundId , 
 		@existT _ _ _ StakingContract_ι_StakeInfo_ι_stake 
 	  ]   ;  
 	 ctor := @StakingContract_ι_StakeInfoC XInteger32 XInteger64   
  }   . 
Global Instance Acc_StakingContract_ι_StakeInfo_ι_roundId : Accessor StakingContract_ι_StakeInfo_ι_roundId :=  {  acc := ·0  }   . 
Global Instance Acc_StakingContract_ι_StakeInfo_ι_stake : Accessor StakingContract_ι_StakeInfo_ι_stake :=  {  acc := ·1  }   . 
Global Instance Struct_StakingContract : Struct StakingContract :=  { 
 	fields :=  [ 
 		@existT _ _ _ StakingContract_ι_NOM_FRACTION , 
 		@existT _ _ _ StakingContract_ι_NODE_FRACTION , 
 		@existT _ _ _ StakingContract_ι_REMOVE_STAKE_FEE , 
 		@existT _ _ _ StakingContract_ι_ADD_STAKE_FEE , 
 		@existT _ _ _ StakingContract_ι_PAUSE_STAKE_FEE , 
 		@existT _ _ _ StakingContract_ι_CONTINUE_STAKE_FEE , 
 		@existT _ _ _ StakingContract_ι_SET_REINVEST_FEE , 
 		@existT _ _ _ StakingContract_ι_NOTIFY_FEE , 
 		@existT _ _ _ StakingContract_ι_MIN_VAL_STAKE , 
 		@existT _ _ _ StakingContract_ι_MAX_MSGS_PER_TR , 
 		@existT _ _ _ StakingContract_ι_NODE_WALLET_MIN_STAKE , 
 		@existT _ _ _ StakingContract_ι_TICKTOCK_PERIOD , 
 		@existT _ _ _ StakingContract_ι_ROUND_UP_VALUE , 
 		@existT _ _ _ StakingContract_ι_ANSWER_MSG_FEE , 
 		@existT _ _ _ StakingContract_ι_STATUS_SUCCESS , 
 
 		@existT _ _ _ StakingContract_ι_STATUS_NO_ACTIVE_ROUNDS , 
 		@existT _ _ _ StakingContract_ι_STATUS_POOL_CLOSED , 
 		@existT _ _ _ StakingContract_ι_STATUS_ROUND_STAKE_LIMIT , 
 		@existT _ _ _ StakingContract_ι_STATUS_MSG_VAL_TOO_SMALL , 
 		@existT _ _ _ StakingContract_ι_STATUS_NO_STAKE , 
 		@existT _ _ _ StakingContract_ι_m_poolClosed , 
 		@existT _ _ _ StakingContract_ι_m_requests , 
 
 		@existT _ _ _ StakingContract_ι_m_minStake , 
 		@existT _ _ _ StakingContract_ι_m_minRoundStake , 
 		@existT _ _ _ StakingContract_ι_m_maxRoundStake , 
 		@existT _ _ _ StakingContract_ι_m_lastRoundInterest 
 
 
 
 	 ]   ;  
 	ctor := @StakingContractC XInteger XInteger64 XInteger8 XBool XArray
 }   . 
Global Instance Acc_StakingContract_ι_NOM_FRACTION : Accessor StakingContract_ι_NOM_FRACTION :=  {  acc := ·0  }   . 
Global Instance Acc_StakingContract_ι_NODE_FRACTION : Accessor StakingContract_ι_NODE_FRACTION :=  {  acc := ·1  }   . 
Global Instance Acc_StakingContract_ι_REMOVE_STAKE_FEE : Accessor StakingContract_ι_REMOVE_STAKE_FEE :=  {  acc := ·2  }   . 
Global Instance Acc_StakingContract_ι_ADD_STAKE_FEE : Accessor StakingContract_ι_ADD_STAKE_FEE :=  {  acc := ·3  }   . 
Global Instance Acc_StakingContract_ι_PAUSE_STAKE_FEE : Accessor StakingContract_ι_PAUSE_STAKE_FEE :=  {  acc := ·4  }   . 
Global Instance Acc_StakingContract_ι_CONTINUE_STAKE_FEE : Accessor StakingContract_ι_CONTINUE_STAKE_FEE :=  {  acc := ·5  }   . 
Global Instance Acc_StakingContract_ι_SET_REINVEST_FEE : Accessor StakingContract_ι_SET_REINVEST_FEE :=  {  acc := ·6  }   . 
Global Instance Acc_StakingContract_ι_NOTIFY_FEE : Accessor StakingContract_ι_NOTIFY_FEE :=  {  acc := ·7  }   . 
Global Instance Acc_StakingContract_ι_MIN_VAL_STAKE : Accessor StakingContract_ι_MIN_VAL_STAKE :=  {  acc := ·8  }   . 
Global Instance Acc_StakingContract_ι_MAX_MSGS_PER_TR : Accessor StakingContract_ι_MAX_MSGS_PER_TR :=  {  acc := ·9  }   . 
Global Instance Acc_StakingContract_ι_NODE_WALLET_MIN_STAKE : Accessor StakingContract_ι_NODE_WALLET_MIN_STAKE :=  {  acc := ·10  }   . 
Global Instance Acc_StakingContract_ι_TICKTOCK_PERIOD : Accessor StakingContract_ι_TICKTOCK_PERIOD :=  {  acc := ·11  }   . 
Global Instance Acc_StakingContract_ι_ROUND_UP_VALUE : Accessor StakingContract_ι_ROUND_UP_VALUE :=  {  acc := ·12  }   . 
Global Instance Acc_StakingContract_ι_ANSWER_MSG_FEE : Accessor StakingContract_ι_ANSWER_MSG_FEE :=  {  acc := ·13  }   . 
Global Instance Acc_StakingContract_ι_STATUS_SUCCESS : Accessor StakingContract_ι_STATUS_SUCCESS :=  {  acc := ·14  }   . 
Global Instance Acc_StakingContract_ι_STATUS_NO_ACTIVE_ROUNDS : Accessor StakingContract_ι_STATUS_NO_ACTIVE_ROUNDS :=  {  acc := ·15  }   . 
Global Instance Acc_StakingContract_ι_STATUS_POOL_CLOSED : Accessor StakingContract_ι_STATUS_POOL_CLOSED :=  {  acc := ·16  }   . 
Global Instance Acc_StakingContract_ι_STATUS_ROUND_STAKE_LIMIT : Accessor StakingContract_ι_STATUS_ROUND_STAKE_LIMIT :=  {  acc := ·17  }   . 
Global Instance Acc_StakingContract_ι_STATUS_MSG_VAL_TOO_SMALL : Accessor StakingContract_ι_STATUS_MSG_VAL_TOO_SMALL :=  {  acc := ·18  }   . 
Global Instance Acc_StakingContract_ι_STATUS_NO_STAKE : Accessor StakingContract_ι_STATUS_NO_STAKE :=  {  acc := ·19  }   . 
Global Instance Acc_StakingContract_ι_m_poolClosed : Accessor StakingContract_ι_m_poolClosed :=  {  acc := ·20  }   . 
Global Instance Acc_StakingContract_ι_m_requests : Accessor StakingContract_ι_m_requests :=  {  acc := ·21  }   . 
Global Instance Acc_StakingContract_ι_m_minStake : Accessor StakingContract_ι_m_minStake :=  {  acc := ·22  }   . 
Global Instance Acc_StakingContract_ι_m_minRoundStake : Accessor StakingContract_ι_m_minRoundStake :=  {  acc := ·23  }   . 
Global Instance Acc_StakingContract_ι_m_maxRoundStake : Accessor StakingContract_ι_m_maxRoundStake :=  {  acc := ·24  }   . 
Global Instance Acc_StakingContract_ι_m_lastRoundInterest : Accessor StakingContract_ι_m_lastRoundInterest :=  {  acc := ·25  }   . 
Instance StakingContract_ι_Node_default : XDefault StakingContract_ι_Node :=  {  
 	 default := StakingContract_ι_NodeC default default  
  }   . 
Instance StakingContract_ι_StakeInfo_default : XDefault StakingContract_ι_StakeInfo :=  {  
 	 default := StakingContract_ι_StakeInfoC default default  
  }   . 
Instance StakingContract_default : XDefault StakingContract :=  {  
 	 default := StakingContractC default default default default default default default default default default default default default default default default default default default default default default default default default default  
  }   . 
End StakingContractClass .


