Require Import Coq.Program.Basics.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Program.Combinators.
Require Import FinProof.ProgrammingWith.

Local Open Scope record.
Local Open Scope program_scope. 

Require Import FinProof.Common.
Require Import FinProof.StateMonad2.
Require Import MultiSigWallet.SolidityNotations.


    
Record OwnerBase·OwnerP  { A I64 }  := OwnerBase·OwnerC  { 
 	OwnerBase·Owner·addr : A  ;   ( *payable* )  
 	OwnerBase·Owner·reward : I64  ;  
  }  .  
 
 Arguments  OwnerBase·OwnerC   [   A I64   ]    . 
Record  OwnerBaseP {  }  := OwnerBaseC  { 
 	OwnerBase·m_owner :   ; 
 
 }   . 
 Arguments OwnerBaseC  [    ]   . 
Module OwnerBaseClass (xt: XTypesSig) (sm: StateMonadSig) . 
Definition  OwnerBase·Owner  := @OwnerBase·OwnerP  XAddress XInteger64  . 
Definition  OwnerBase  := @OwnerBaseP    . 
Global Instance Struct_OwnerBase·Owner : Struct OwnerBase·Owner :=  {  
 	 fields :=  [  
 		@existT _ _ _ OwnerBase·Owner·addr , 
 		@existT _ _ _ OwnerBase·Owner·reward , 
 	  ]   ;  
 	 ctor := @OwnerBase·OwnerC XAddress XInteger64   
  }   . 
Global Instance Acc_OwnerBase·Owner·addr : Accessor OwnerBase·Owner·addr :=  {  acc := ·0  }   . 
Global Instance Acc_OwnerBase·Owner·reward : Accessor OwnerBase·Owner·reward :=  {  acc := ·1  }   . 
Global Instance Struct_OwnerBase : Struct OwnerBase :=  { 
 	fields :=  [ 
 		@existT _ _ _ OwnerBase·m_owner , 
 
 	 ]   ;  
 	ctor := @OwnerBaseC 
 }   . 
Global Instance Acc_OwnerBase·m_owner : Accessor OwnerBase·m_owner :=  {  acc := ·0  }   . 
Bind Scope struct_scope with OwnerBase·Owner  . 
Instance OwnerBase·Owner_default : XDefault OwnerBase·Owner :=  {  
 	 default := OwnerBase·OwnerC default default  
  }   . 
Instance OwnerBase_default : XDefault OwnerBase :=  {  
 	 default := OwnerBaseC default  
  }   . 
End OwnerBaseClass .

 
Record ElectorBase·RequestP  { I64 I256 I32 I8 }  := ElectorBase·RequestC  { 
 	ElectorBase·Request·queryId : I64  ;  
 	ElectorBase·Request·validatorKey : I256  ;  
 	ElectorBase·Request·stakeAt : I32  ;  
 	ElectorBase·Request·maxFactor : I32  ;  
 	ElectorBase·Request·adnlAddr : I256  ;  
 	ElectorBase·Request·signature : I8  ;  
  }  .  
 
 Arguments  ElectorBase·RequestC   [   I64 I256 I32 I8   ]    . 
Record  ElectorBaseP { I64 A }  := ElectorBaseC  { 
 	ElectorBase·RECOVER_STAKE_MSG_VALUE : I64  ;   ( *constant := 1e9* ) 
 	ElectorBase·m_elector : A  ;   ( *payable* ) 
 
 }   . 
 Arguments ElectorBaseC  [  I64 A  ]   . 
Module ElectorBaseClass (xt: XTypesSig) (sm: StateMonadSig) . 
Definition  ElectorBase·Request  := @ElectorBase·RequestP  XInteger64 XInteger256 XInteger32 XInteger8  . 
Definition  ElectorBase  := @ElectorBaseP  XInteger64 XAddress  . 
Global Instance Struct_ElectorBase·Request : Struct ElectorBase·Request :=  {  
 	 fields :=  [  
 		@existT _ _ _ ElectorBase·Request·queryId , 
 		@existT _ _ _ ElectorBase·Request·validatorKey , 
 		@existT _ _ _ ElectorBase·Request·stakeAt , 
 		@existT _ _ _ ElectorBase·Request·maxFactor , 
 		@existT _ _ _ ElectorBase·Request·adnlAddr , 
 		@existT _ _ _ ElectorBase·Request·signature , 
 	  ]   ;  
 	 ctor := @ElectorBase·RequestC XInteger64 XInteger256 XInteger32 XInteger8   
  }   . 
Global Instance Acc_ElectorBase·Request·queryId : Accessor ElectorBase·Request·queryId :=  {  acc := ·0  }   . 
Global Instance Acc_ElectorBase·Request·validatorKey : Accessor ElectorBase·Request·validatorKey :=  {  acc := ·1  }   . 
Global Instance Acc_ElectorBase·Request·stakeAt : Accessor ElectorBase·Request·stakeAt :=  {  acc := ·2  }   . 
Global Instance Acc_ElectorBase·Request·maxFactor : Accessor ElectorBase·Request·maxFactor :=  {  acc := ·3  }   . 
Global Instance Acc_ElectorBase·Request·adnlAddr : Accessor ElectorBase·Request·adnlAddr :=  {  acc := ·4  }   . 
Global Instance Acc_ElectorBase·Request·signature : Accessor ElectorBase·Request·signature :=  {  acc := ·5  }   . 
Global Instance Struct_ElectorBase : Struct ElectorBase :=  { 
 	fields :=  [ 
 		@existT _ _ _ ElectorBase·RECOVER_STAKE_MSG_VALUE , 
 		@existT _ _ _ ElectorBase·m_elector , 
 
 	 ]   ;  
 	ctor := @ElectorBaseC I64 A
 }   . 
Global Instance Acc_ElectorBase·RECOVER_STAKE_MSG_VALUE : Accessor ElectorBase·RECOVER_STAKE_MSG_VALUE :=  {  acc := ·0  }   . 
Global Instance Acc_ElectorBase·m_elector : Accessor ElectorBase·m_elector :=  {  acc := ·1  }   . 
Bind Scope struct_scope with ElectorBase·Request  . 
Instance ElectorBase·Request_default : XDefault ElectorBase·Request :=  {  
 	 default := ElectorBase·RequestC default default default default default default  
  }   . 
Instance ElectorBase_default : XDefault ElectorBase :=  {  
 	 default := ElectorBaseC default default  
  }   . 
End ElectorBaseClass .

 
Record ElectionParams·ValidatorDescr73P  { I8 I32 I256 I64 }  := ElectionParams·ValidatorDescr73C  { 
 	ElectionParams·ValidatorDescr73·validator_addr73 : I8  ;  
 	ElectionParams·ValidatorDescr73·ed25519_pubkey : I32  ;  
 	ElectionParams·ValidatorDescr73·pubkey : I256  ;  
 	ElectionParams·ValidatorDescr73·weight : I64  ;  
 	ElectionParams·ValidatorDescr73·adnl_addr : I256  ;  
  }  .  
 
 Arguments  ElectionParams·ValidatorDescr73C   [   I8 I32 I256 I64   ]    . 
Record  ElectionParamsP { I32 }  := ElectionParamsC  { 
 	ElectionParams·m_electAt : I32  ; 
 	ElectionParams·m_beginBefore : I32  ; 
 	ElectionParams·m_endBefore : I32  ; 
 	ElectionParams·m_electedFor : I32  ; 
 	ElectionParams·m_heldFor : I32  ; 
 
 }   . 
 Arguments ElectionParamsC  [  I32  ]   . 
Module ElectionParamsClass (xt: XTypesSig) (sm: StateMonadSig) . 
Definition  ElectionParams·ValidatorDescr73  := @ElectionParams·ValidatorDescr73P  XInteger8 XInteger32 XInteger256 XInteger64  . 
Definition  ElectionParams  := @ElectionParamsP  XInteger32  . 
Global Instance Struct_ElectionParams·ValidatorDescr73 : Struct ElectionParams·ValidatorDescr73 :=  {  
 	 fields :=  [  
 		@existT _ _ _ ElectionParams·ValidatorDescr73·validator_addr73 , 
 		@existT _ _ _ ElectionParams·ValidatorDescr73·ed25519_pubkey , 
 		@existT _ _ _ ElectionParams·ValidatorDescr73·pubkey , 
 		@existT _ _ _ ElectionParams·ValidatorDescr73·weight , 
 		@existT _ _ _ ElectionParams·ValidatorDescr73·adnl_addr , 
 	  ]   ;  
 	 ctor := @ElectionParams·ValidatorDescr73C XInteger8 XInteger32 XInteger256 XInteger64   
  }   . 
Global Instance Acc_ElectionParams·ValidatorDescr73·validator_addr73 : Accessor ElectionParams·ValidatorDescr73·validator_addr73 :=  {  acc := ·0  }   . 
Global Instance Acc_ElectionParams·ValidatorDescr73·ed25519_pubkey : Accessor ElectionParams·ValidatorDescr73·ed25519_pubkey :=  {  acc := ·1  }   . 
Global Instance Acc_ElectionParams·ValidatorDescr73·pubkey : Accessor ElectionParams·ValidatorDescr73·pubkey :=  {  acc := ·2  }   . 
Global Instance Acc_ElectionParams·ValidatorDescr73·weight : Accessor ElectionParams·ValidatorDescr73·weight :=  {  acc := ·3  }   . 
Global Instance Acc_ElectionParams·ValidatorDescr73·adnl_addr : Accessor ElectionParams·ValidatorDescr73·adnl_addr :=  {  acc := ·4  }   . 
Global Instance Struct_ElectionParams : Struct ElectionParams :=  { 
 	fields :=  [ 
 		@existT _ _ _ ElectionParams·m_electAt , 
 		@existT _ _ _ ElectionParams·m_beginBefore , 
 		@existT _ _ _ ElectionParams·m_endBefore , 
 		@existT _ _ _ ElectionParams·m_electedFor , 
 		@existT _ _ _ ElectionParams·m_heldFor , 
 
 	 ]   ;  
 	ctor := @ElectionParamsC I32
 }   . 
Global Instance Acc_ElectionParams·m_electAt : Accessor ElectionParams·m_electAt :=  {  acc := ·0  }   . 
Global Instance Acc_ElectionParams·m_beginBefore : Accessor ElectionParams·m_beginBefore :=  {  acc := ·1  }   . 
Global Instance Acc_ElectionParams·m_endBefore : Accessor ElectionParams·m_endBefore :=  {  acc := ·2  }   . 
Global Instance Acc_ElectionParams·m_electedFor : Accessor ElectionParams·m_electedFor :=  {  acc := ·3  }   . 
Global Instance Acc_ElectionParams·m_heldFor : Accessor ElectionParams·m_heldFor :=  {  acc := ·4  }   . 
Bind Scope struct_scope with ElectionParams·ValidatorDescr73  . 
Instance ElectionParams·ValidatorDescr73_default : XDefault ElectionParams·ValidatorDescr73 :=  {  
 	 default := ElectionParams·ValidatorDescr73C default default default default default  
  }   . 
Instance ElectionParams_default : XDefault ElectionParams :=  {  
 	 default := ElectionParamsC default default default default default  
  }   . 
End ElectionParamsClass .

 
Record StakeholderBase·StakeholderP  { I64 B }  := StakeholderBase·StakeholderC  { 
 	StakeholderBase·Stakeholder·totalStake : I64  ;  
 	StakeholderBase·Stakeholder·unusedStake : I64  ;  
 	StakeholderBase·Stakeholder·reinvest : B  ;  
 	StakeholderBase·Stakeholder·reward : I64  ;  
  }  .  
 
 Arguments  StakeholderBase·StakeholderC   [   I64 B   ]    . 
Record  StakeholderBaseP { Arr }  := StakeholderBaseC  { 
 	StakeholderBase·m_stakeholders : Arr A   ; 
 }   . 
 Arguments StakeholderBaseC  [  Arr  ]   . 
Module StakeholderBaseClass (xt: XTypesSig) (sm: StateMonadSig) . 
Definition  StakeholderBase·Stakeholder  := @StakeholderBase·StakeholderP  XInteger64 XBool  . 
Definition  StakeholderBase  := @StakeholderBaseP  XArray  . 
Global Instance Struct_StakeholderBase·Stakeholder : Struct StakeholderBase·Stakeholder :=  {  
 	 fields :=  [  
 		@existT _ _ _ StakeholderBase·Stakeholder·totalStake , 
 		@existT _ _ _ StakeholderBase·Stakeholder·unusedStake , 
 		@existT _ _ _ StakeholderBase·Stakeholder·reinvest , 
 		@existT _ _ _ StakeholderBase·Stakeholder·reward , 
 	  ]   ;  
 	 ctor := @StakeholderBase·StakeholderC XInteger64 XBool   
  }   . 
Global Instance Acc_StakeholderBase·Stakeholder·totalStake : Accessor StakeholderBase·Stakeholder·totalStake :=  {  acc := ·0  }   . 
Global Instance Acc_StakeholderBase·Stakeholder·unusedStake : Accessor StakeholderBase·Stakeholder·unusedStake :=  {  acc := ·1  }   . 
Global Instance Acc_StakeholderBase·Stakeholder·reinvest : Accessor StakeholderBase·Stakeholder·reinvest :=  {  acc := ·2  }   . 
Global Instance Acc_StakeholderBase·Stakeholder·reward : Accessor StakeholderBase·Stakeholder·reward :=  {  acc := ·3  }   . 
Global Instance Struct_StakeholderBase : Struct StakeholderBase :=  { 
 	fields :=  [ 
 		@existT _ _ _ StakeholderBase·m_stakeholders , 
 	 ]   ;  
 	ctor := @StakeholderBaseC Arr
 }   . 
Global Instance Acc_StakeholderBase·m_stakeholders : Accessor StakeholderBase·m_stakeholders :=  {  acc := ·0  }   . 
Bind Scope struct_scope with StakeholderBase·Stakeholder  . 
Instance StakeholderBase·Stakeholder_default : XDefault StakeholderBase·Stakeholder :=  {  
 	 default := StakeholderBase·StakeholderC default default default default  
  }   . 
Instance StakeholderBase_default : XDefault StakeholderBase :=  {  
 	 default := StakeholderBaseC default  
  }   . 
End StakeholderBaseClass .

 
Record RoundsBase·RoundP  { I32 I8 I64 Arr A }  := RoundsBase·RoundC  { 
 	RoundsBase·Round·id : I32  ;  
 	RoundsBase·Round·step : I8  ;  
 	RoundsBase·Round·count : I32  ;  
 	RoundsBase·Round·totalStake : I64  ;  
 	RoundsBase·Round·rewards : I64  ;  
 	RoundsBase·Round·unused : I64  ;  
 	RoundsBase·Round·completionStatus : I8  ;  
 	RoundsBase·Round·start : I32  ;  
 	RoundsBase·Round·end : I32  ;  
 	RoundsBase·Round·stakes : Arr A I64  ;  
  }  .  
 
 Arguments  RoundsBase·RoundC   [   I32 I8 I64 Arr A   ]    . 
Record RoundsBase·RoundInfoP  { I32 I8 I64 }  := RoundsBase·RoundInfoC  { 
 	RoundsBase·RoundInfo·id : I32  ;  
 	RoundsBase·RoundInfo·start : I32  ;  
 	RoundsBase·RoundInfo·end : I32  ;  
 	RoundsBase·RoundInfo·step : I8  ;  
 	RoundsBase·RoundInfo·completionStatus : I8  ;  
 	RoundsBase·RoundInfo·stake : I64  ;  
 	RoundsBase·RoundInfo·stakeholderCount : I32  ;  
 	RoundsBase·RoundInfo·rewards : I64  ;  
  }  .  
 
 Arguments  RoundsBase·RoundInfoC   [   I32 I8 I64   ]    . 
Record  RoundsBaseP { I8 Arr I64 }  := RoundsBaseC  { 
 	RoundsBase·STEP_POOLING : I8  ;   ( *constant := 0* ) 
 	RoundsBase·STEP_WAITING_REQUESTS : I8  ;   ( *constant := 1* ) 
 	RoundsBase·STEP_ELECTIONS : I8  ;   ( *constant := 2* ) 
 	RoundsBase·STEP_WAITING_ELECTION_RESULTS : I8  ;   ( *constant := 3* ) 
 	RoundsBase·STEP_WAITING_UNFREEZE : I8  ;   ( *constant := 4* ) 
 	RoundsBase·STEP_COMPLETED : I8  ;   ( *constant := 5* ) 
 	RoundsBase·STEP_COMPLETING : I8  ;   ( *constant := 6* ) 
 	RoundsBase·ROUND_UNDEFINED : I8  ;   ( *constant := 0* ) 
 	RoundsBase·ROUND_RECEIVED_REWARD : I8  ;   ( *constant := 7* ) 
 	RoundsBase·ROUND_POOL_CLOSED : I8  ;   ( *constant := 1* ) 
 	RoundsBase·ROUND_MISSED_ELECTIONS : I8  ;   ( *constant := 2* ) 
 	RoundsBase·ROUND_NOT_ENOUGH_TOTAL_STAKE : I8  ;   ( *constant := 3* ) 
 	RoundsBase·ROUND_NODE_STAKE_TOO_SMALL : I8  ;   ( *constant := 4* ) 
 	RoundsBase·ROUND_STAKE_REJECTED : I8  ;   ( *constant := 5* ) 
 	RoundsBase·ROUND_LOST_ELECTIONS : I8  ;   ( *constant := 6* ) 
 	RoundsBase·m_rounds : Arr I64   ; 
 	RoundsBase·m_startIdx : I64  ; 
 	RoundsBase·m_roundsCount : I8  ; 
 	RoundsBase·m_pendingRounds : Arr I32   ; 
 }   . 
 Arguments RoundsBaseC  [  I8 Arr I64  ]   . 
Module RoundsBaseClass (xt: XTypesSig) (sm: StateMonadSig) . 
Definition  RoundsBase·Round  := @RoundsBase·RoundP  XInteger32 XInteger8 XInteger64 XArray XAddress  . 
Definition  RoundsBase·RoundInfo  := @RoundsBase·RoundInfoP  XInteger32 XInteger8 XInteger64  . 
Definition  RoundsBase  := @RoundsBaseP  XInteger8 XArray XInteger64  . 
Global Instance Struct_RoundsBase·Round : Struct RoundsBase·Round :=  {  
 	 fields :=  [  
 		@existT _ _ _ RoundsBase·Round·id , 
 		@existT _ _ _ RoundsBase·Round·step , 
 		@existT _ _ _ RoundsBase·Round·count , 
 		@existT _ _ _ RoundsBase·Round·totalStake , 
 		@existT _ _ _ RoundsBase·Round·rewards , 
 		@existT _ _ _ RoundsBase·Round·unused , 
 		@existT _ _ _ RoundsBase·Round·completionStatus , 
 		@existT _ _ _ RoundsBase·Round·start , 
 		@existT _ _ _ RoundsBase·Round·end , 
 		@existT _ _ _ RoundsBase·Round·stakes , 
 	  ]   ;  
 	 ctor := @RoundsBase·RoundC XInteger32 XInteger8 XInteger64 XArray XAddress   
  }   . 
Global Instance Acc_RoundsBase·Round·id : Accessor RoundsBase·Round·id :=  {  acc := ·0  }   . 
Global Instance Acc_RoundsBase·Round·step : Accessor RoundsBase·Round·step :=  {  acc := ·1  }   . 
Global Instance Acc_RoundsBase·Round·count : Accessor RoundsBase·Round·count :=  {  acc := ·2  }   . 
Global Instance Acc_RoundsBase·Round·totalStake : Accessor RoundsBase·Round·totalStake :=  {  acc := ·3  }   . 
Global Instance Acc_RoundsBase·Round·rewards : Accessor RoundsBase·Round·rewards :=  {  acc := ·4  }   . 
Global Instance Acc_RoundsBase·Round·unused : Accessor RoundsBase·Round·unused :=  {  acc := ·5  }   . 
Global Instance Acc_RoundsBase·Round·completionStatus : Accessor RoundsBase·Round·completionStatus :=  {  acc := ·6  }   . 
Global Instance Acc_RoundsBase·Round·start : Accessor RoundsBase·Round·start :=  {  acc := ·7  }   . 
Global Instance Acc_RoundsBase·Round·end : Accessor RoundsBase·Round·end :=  {  acc := ·8  }   . 
Global Instance Acc_RoundsBase·Round·stakes : Accessor RoundsBase·Round·stakes :=  {  acc := ·9  }   . 
Global Instance Struct_RoundsBase·RoundInfo : Struct RoundsBase·RoundInfo :=  {  
 	 fields :=  [  
 		@existT _ _ _ RoundsBase·RoundInfo·id , 
 		@existT _ _ _ RoundsBase·RoundInfo·start , 
 		@existT _ _ _ RoundsBase·RoundInfo·end , 
 		@existT _ _ _ RoundsBase·RoundInfo·step , 
 		@existT _ _ _ RoundsBase·RoundInfo·completionStatus , 
 		@existT _ _ _ RoundsBase·RoundInfo·stake , 
 		@existT _ _ _ RoundsBase·RoundInfo·stakeholderCount , 
 		@existT _ _ _ RoundsBase·RoundInfo·rewards , 
 	  ]   ;  
 	 ctor := @RoundsBase·RoundInfoC XInteger32 XInteger8 XInteger64   
  }   . 
Global Instance Acc_RoundsBase·RoundInfo·id : Accessor RoundsBase·RoundInfo·id :=  {  acc := ·0  }   . 
Global Instance Acc_RoundsBase·RoundInfo·start : Accessor RoundsBase·RoundInfo·start :=  {  acc := ·1  }   . 
Global Instance Acc_RoundsBase·RoundInfo·end : Accessor RoundsBase·RoundInfo·end :=  {  acc := ·2  }   . 
Global Instance Acc_RoundsBase·RoundInfo·step : Accessor RoundsBase·RoundInfo·step :=  {  acc := ·3  }   . 
Global Instance Acc_RoundsBase·RoundInfo·completionStatus : Accessor RoundsBase·RoundInfo·completionStatus :=  {  acc := ·4  }   . 
Global Instance Acc_RoundsBase·RoundInfo·stake : Accessor RoundsBase·RoundInfo·stake :=  {  acc := ·5  }   . 
Global Instance Acc_RoundsBase·RoundInfo·stakeholderCount : Accessor RoundsBase·RoundInfo·stakeholderCount :=  {  acc := ·6  }   . 
Global Instance Acc_RoundsBase·RoundInfo·rewards : Accessor RoundsBase·RoundInfo·rewards :=  {  acc := ·7  }   . 
Global Instance Struct_RoundsBase : Struct RoundsBase :=  { 
 	fields :=  [ 
 		@existT _ _ _ RoundsBase·STEP_POOLING , 
 		@existT _ _ _ RoundsBase·STEP_WAITING_REQUESTS , 
 		@existT _ _ _ RoundsBase·STEP_ELECTIONS , 
 		@existT _ _ _ RoundsBase·STEP_WAITING_ELECTION_RESULTS , 
 		@existT _ _ _ RoundsBase·STEP_WAITING_UNFREEZE , 
 		@existT _ _ _ RoundsBase·STEP_COMPLETED , 
 		@existT _ _ _ RoundsBase·STEP_COMPLETING , 
 		@existT _ _ _ RoundsBase·ROUND_UNDEFINED , 
 		@existT _ _ _ RoundsBase·ROUND_RECEIVED_REWARD , 
 		@existT _ _ _ RoundsBase·ROUND_POOL_CLOSED , 
 		@existT _ _ _ RoundsBase·ROUND_MISSED_ELECTIONS , 
 		@existT _ _ _ RoundsBase·ROUND_NOT_ENOUGH_TOTAL_STAKE , 
 		@existT _ _ _ RoundsBase·ROUND_NODE_STAKE_TOO_SMALL , 
 		@existT _ _ _ RoundsBase·ROUND_STAKE_REJECTED , 
 		@existT _ _ _ RoundsBase·ROUND_LOST_ELECTIONS , 
 		@existT _ _ _ RoundsBase·m_rounds , 
 		@existT _ _ _ RoundsBase·m_startIdx , 
 		@existT _ _ _ RoundsBase·m_roundsCount , 
 		@existT _ _ _ RoundsBase·m_pendingRounds , 
 	 ]   ;  
 	ctor := @RoundsBaseC I8 Arr I64
 }   . 
Global Instance Acc_RoundsBase·STEP_POOLING : Accessor RoundsBase·STEP_POOLING :=  {  acc := ·0  }   . 
Global Instance Acc_RoundsBase·STEP_WAITING_REQUESTS : Accessor RoundsBase·STEP_WAITING_REQUESTS :=  {  acc := ·1  }   . 
Global Instance Acc_RoundsBase·STEP_ELECTIONS : Accessor RoundsBase·STEP_ELECTIONS :=  {  acc := ·2  }   . 
Global Instance Acc_RoundsBase·STEP_WAITING_ELECTION_RESULTS : Accessor RoundsBase·STEP_WAITING_ELECTION_RESULTS :=  {  acc := ·3  }   . 
Global Instance Acc_RoundsBase·STEP_WAITING_UNFREEZE : Accessor RoundsBase·STEP_WAITING_UNFREEZE :=  {  acc := ·4  }   . 
Global Instance Acc_RoundsBase·STEP_COMPLETED : Accessor RoundsBase·STEP_COMPLETED :=  {  acc := ·5  }   . 
Global Instance Acc_RoundsBase·STEP_COMPLETING : Accessor RoundsBase·STEP_COMPLETING :=  {  acc := ·6  }   . 
Global Instance Acc_RoundsBase·ROUND_UNDEFINED : Accessor RoundsBase·ROUND_UNDEFINED :=  {  acc := ·7  }   . 
Global Instance Acc_RoundsBase·ROUND_RECEIVED_REWARD : Accessor RoundsBase·ROUND_RECEIVED_REWARD :=  {  acc := ·8  }   . 
Global Instance Acc_RoundsBase·ROUND_POOL_CLOSED : Accessor RoundsBase·ROUND_POOL_CLOSED :=  {  acc := ·9  }   . 
Global Instance Acc_RoundsBase·ROUND_MISSED_ELECTIONS : Accessor RoundsBase·ROUND_MISSED_ELECTIONS :=  {  acc := ·10  }   . 
Global Instance Acc_RoundsBase·ROUND_NOT_ENOUGH_TOTAL_STAKE : Accessor RoundsBase·ROUND_NOT_ENOUGH_TOTAL_STAKE :=  {  acc := ·11  }   . 
Global Instance Acc_RoundsBase·ROUND_NODE_STAKE_TOO_SMALL : Accessor RoundsBase·ROUND_NODE_STAKE_TOO_SMALL :=  {  acc := ·12  }   . 
Global Instance Acc_RoundsBase·ROUND_STAKE_REJECTED : Accessor RoundsBase·ROUND_STAKE_REJECTED :=  {  acc := ·13  }   . 
Global Instance Acc_RoundsBase·ROUND_LOST_ELECTIONS : Accessor RoundsBase·ROUND_LOST_ELECTIONS :=  {  acc := ·14  }   . 
Global Instance Acc_RoundsBase·m_rounds : Accessor RoundsBase·m_rounds :=  {  acc := ·15  }   . 
Global Instance Acc_RoundsBase·m_startIdx : Accessor RoundsBase·m_startIdx :=  {  acc := ·16  }   . 
Global Instance Acc_RoundsBase·m_roundsCount : Accessor RoundsBase·m_roundsCount :=  {  acc := ·17  }   . 
Global Instance Acc_RoundsBase·m_pendingRounds : Accessor RoundsBase·m_pendingRounds :=  {  acc := ·18  }   . 
Bind Scope struct_scope with RoundsBase·Round  . 
Bind Scope struct_scope with RoundsBase·RoundInfo  . 
Instance RoundsBase·Round_default : XDefault RoundsBase·Round :=  {  
 	 default := RoundsBase·RoundC default default default default default default default default default default  
  }   . 
Instance RoundsBase·RoundInfo_default : XDefault RoundsBase·RoundInfo :=  {  
 	 default := RoundsBase·RoundInfoC default default default default default default default default  
  }   . 
Instance RoundsBase_default : XDefault RoundsBase :=  {  
 	 default := RoundsBaseC default default default default default default default default default default default default default default default default default default default  
  }   . 
End RoundsBaseClass .

 
Record StakingContract·NodeP  { A I32 }  := StakingContract·NodeC  { 
 	StakingContract·Node·wallet : A  ;  
 	StakingContract·Node·factor : I32  ;  
   }  .  
 
 Arguments  StakingContract·NodeC   [   A I32   ]    . 
Record StakingContract·StakeInfoP  { I32 I64 }  := StakingContract·StakeInfoC  { 
 	StakingContract·StakeInfo·roundId : I32  ;  
 	StakingContract·StakeInfo·stake : I64  ;  
  }  .  
 
 Arguments  StakingContract·StakeInfoC   [   I32 I64   ]    . 
Record  StakingContractP { I I64 I8 B Arr }  := StakingContractC  { 
 	StakingContract·NOM_FRACTION : I  ;   ( *constant := 70* ) 
 	StakingContract·NODE_FRACTION : I  ;   ( *constant := 25* ) 
 	StakingContract·REMOVE_STAKE_FEE : I64  ;   ( *constant := 3e7* ) 
 	StakingContract·ADD_STAKE_FEE : I64  ;   ( *constant := 3e8* ) 
 	StakingContract·PAUSE_STAKE_FEE : I64  ;   ( *constant := 3e7* ) 
 	StakingContract·CONTINUE_STAKE_FEE : I64  ;   ( *constant := 3e7* ) 
 	StakingContract·SET_REINVEST_FEE : I64  ;   ( *constant := 3e7* ) 
 	StakingContract·NOTIFY_FEE : I64  ;   ( *constant := 3e6* ) 
 	StakingContract·MIN_VAL_STAKE : I  ;   ( *constant := 10001000000000* ) 
 	StakingContract·MAX_MSGS_PER_TR : I8  ;   ( *constant := 40* ) 
 	StakingContract·NODE_WALLET_MIN_STAKE : I8  ;   ( *constant := 20* ) 
 	StakingContract·TICKTOCK_PERIOD : I  ;   ( *constant := 30* ) 
 	StakingContract·ROUND_UP_VALUE : I64  ;   ( *constant := 1e9* ) 
 	StakingContract·ANSWER_MSG_FEE : I64  ;   ( *constant := 3e6* ) 
 	StakingContract·STATUS_SUCCESS : I8  ;   ( *constant := 0* ) 
 
 	StakingContract·STATUS_NO_ACTIVE_ROUNDS : I8  ;   ( *constant := 2* ) 
 	StakingContract·STATUS_POOL_CLOSED : I8  ;   ( *constant := 3* ) 
 	StakingContract·STATUS_ROUND_STAKE_LIMIT : I8  ;   ( *constant := 4* ) 
 	StakingContract·STATUS_MSG_VAL_TOO_SMALL : I8  ;   ( *constant := 5* ) 
 	StakingContract·STATUS_NO_STAKE : I8  ;   ( *constant := 6* ) 
 	StakingContract·m_poolClosed : B  ; 
 	StakingContract·m_requests : Arr I32   ; 
 
 	StakingContract·m_minStake : I64  ; 
 	StakingContract·m_minRoundStake : I64  ; 
 	StakingContract·m_maxRoundStake : I64  ; 
 	StakingContract·m_lastRoundInterest : I64  ; 
 
 
 
 }   . 
 Arguments StakingContractC  [  I I64 I8 B Arr  ]   . 
Module StakingContractClass (xt: XTypesSig) (sm: StateMonadSig) . 
Definition  StakingContract·Node  := @StakingContract·NodeP  XAddress XInteger32  . 
Definition  StakingContract·StakeInfo  := @StakingContract·StakeInfoP  XInteger32 XInteger64  . 
Definition  StakingContract  := @StakingContractP  XInteger XInteger64 XInteger8 XBool XArray  . 
Global Instance Struct_StakingContract·Node : Struct StakingContract·Node :=  {  
 	 fields :=  [  
 		@existT _ _ _ StakingContract·Node·wallet , 
 		@existT _ _ _ StakingContract·Node·factor , 
 
 	  ]   ;  
 	 ctor := @StakingContract·NodeC XAddress XInteger32   
  }   . 
Global Instance Acc_StakingContract·Node·wallet : Accessor StakingContract·Node·wallet :=  {  acc := ·0  }   . 
Global Instance Acc_StakingContract·Node·factor : Accessor StakingContract·Node·factor :=  {  acc := ·1  }   . 
Global Instance Struct_StakingContract·StakeInfo : Struct StakingContract·StakeInfo :=  {  
 	 fields :=  [  
 		@existT _ _ _ StakingContract·StakeInfo·roundId , 
 		@existT _ _ _ StakingContract·StakeInfo·stake , 
 	  ]   ;  
 	 ctor := @StakingContract·StakeInfoC XInteger32 XInteger64   
  }   . 
Global Instance Acc_StakingContract·StakeInfo·roundId : Accessor StakingContract·StakeInfo·roundId :=  {  acc := ·0  }   . 
Global Instance Acc_StakingContract·StakeInfo·stake : Accessor StakingContract·StakeInfo·stake :=  {  acc := ·1  }   . 
Global Instance Struct_StakingContract : Struct StakingContract :=  { 
 	fields :=  [ 
 		@existT _ _ _ StakingContract·NOM_FRACTION , 
 		@existT _ _ _ StakingContract·NODE_FRACTION , 
 		@existT _ _ _ StakingContract·REMOVE_STAKE_FEE , 
 		@existT _ _ _ StakingContract·ADD_STAKE_FEE , 
 		@existT _ _ _ StakingContract·PAUSE_STAKE_FEE , 
 		@existT _ _ _ StakingContract·CONTINUE_STAKE_FEE , 
 		@existT _ _ _ StakingContract·SET_REINVEST_FEE , 
 		@existT _ _ _ StakingContract·NOTIFY_FEE , 
 		@existT _ _ _ StakingContract·MIN_VAL_STAKE , 
 		@existT _ _ _ StakingContract·MAX_MSGS_PER_TR , 
 		@existT _ _ _ StakingContract·NODE_WALLET_MIN_STAKE , 
 		@existT _ _ _ StakingContract·TICKTOCK_PERIOD , 
 		@existT _ _ _ StakingContract·ROUND_UP_VALUE , 
 		@existT _ _ _ StakingContract·ANSWER_MSG_FEE , 
 		@existT _ _ _ StakingContract·STATUS_SUCCESS , 
 
 		@existT _ _ _ StakingContract·STATUS_NO_ACTIVE_ROUNDS , 
 		@existT _ _ _ StakingContract·STATUS_POOL_CLOSED , 
 		@existT _ _ _ StakingContract·STATUS_ROUND_STAKE_LIMIT , 
 		@existT _ _ _ StakingContract·STATUS_MSG_VAL_TOO_SMALL , 
 		@existT _ _ _ StakingContract·STATUS_NO_STAKE , 
 		@existT _ _ _ StakingContract·m_poolClosed , 
 		@existT _ _ _ StakingContract·m_requests , 
 
 		@existT _ _ _ StakingContract·m_minStake , 
 		@existT _ _ _ StakingContract·m_minRoundStake , 
 		@existT _ _ _ StakingContract·m_maxRoundStake , 
 		@existT _ _ _ StakingContract·m_lastRoundInterest , 
 
 
 
 	 ]   ;  
 	ctor := @StakingContractC I I64 I8 B Arr
 }   . 
Global Instance Acc_StakingContract·NOM_FRACTION : Accessor StakingContract·NOM_FRACTION :=  {  acc := ·0  }   . 
Global Instance Acc_StakingContract·NODE_FRACTION : Accessor StakingContract·NODE_FRACTION :=  {  acc := ·1  }   . 
Global Instance Acc_StakingContract·REMOVE_STAKE_FEE : Accessor StakingContract·REMOVE_STAKE_FEE :=  {  acc := ·2  }   . 
Global Instance Acc_StakingContract·ADD_STAKE_FEE : Accessor StakingContract·ADD_STAKE_FEE :=  {  acc := ·3  }   . 
Global Instance Acc_StakingContract·PAUSE_STAKE_FEE : Accessor StakingContract·PAUSE_STAKE_FEE :=  {  acc := ·4  }   . 
Global Instance Acc_StakingContract·CONTINUE_STAKE_FEE : Accessor StakingContract·CONTINUE_STAKE_FEE :=  {  acc := ·5  }   . 
Global Instance Acc_StakingContract·SET_REINVEST_FEE : Accessor StakingContract·SET_REINVEST_FEE :=  {  acc := ·6  }   . 
Global Instance Acc_StakingContract·NOTIFY_FEE : Accessor StakingContract·NOTIFY_FEE :=  {  acc := ·7  }   . 
Global Instance Acc_StakingContract·MIN_VAL_STAKE : Accessor StakingContract·MIN_VAL_STAKE :=  {  acc := ·8  }   . 
Global Instance Acc_StakingContract·MAX_MSGS_PER_TR : Accessor StakingContract·MAX_MSGS_PER_TR :=  {  acc := ·9  }   . 
Global Instance Acc_StakingContract·NODE_WALLET_MIN_STAKE : Accessor StakingContract·NODE_WALLET_MIN_STAKE :=  {  acc := ·10  }   . 
Global Instance Acc_StakingContract·TICKTOCK_PERIOD : Accessor StakingContract·TICKTOCK_PERIOD :=  {  acc := ·11  }   . 
Global Instance Acc_StakingContract·ROUND_UP_VALUE : Accessor StakingContract·ROUND_UP_VALUE :=  {  acc := ·12  }   . 
Global Instance Acc_StakingContract·ANSWER_MSG_FEE : Accessor StakingContract·ANSWER_MSG_FEE :=  {  acc := ·13  }   . 
Global Instance Acc_StakingContract·STATUS_SUCCESS : Accessor StakingContract·STATUS_SUCCESS :=  {  acc := ·14  }   . 
Global Instance Acc_StakingContract·STATUS_NO_ACTIVE_ROUNDS : Accessor StakingContract·STATUS_NO_ACTIVE_ROUNDS :=  {  acc := ·15  }   . 
Global Instance Acc_StakingContract·STATUS_POOL_CLOSED : Accessor StakingContract·STATUS_POOL_CLOSED :=  {  acc := ·16  }   . 
Global Instance Acc_StakingContract·STATUS_ROUND_STAKE_LIMIT : Accessor StakingContract·STATUS_ROUND_STAKE_LIMIT :=  {  acc := ·17  }   . 
Global Instance Acc_StakingContract·STATUS_MSG_VAL_TOO_SMALL : Accessor StakingContract·STATUS_MSG_VAL_TOO_SMALL :=  {  acc := ·18  }   . 
Global Instance Acc_StakingContract·STATUS_NO_STAKE : Accessor StakingContract·STATUS_NO_STAKE :=  {  acc := ·19  }   . 
Global Instance Acc_StakingContract·m_poolClosed : Accessor StakingContract·m_poolClosed :=  {  acc := ·20  }   . 
Global Instance Acc_StakingContract·m_requests : Accessor StakingContract·m_requests :=  {  acc := ·21  }   . 
Global Instance Acc_StakingContract·m_minStake : Accessor StakingContract·m_minStake :=  {  acc := ·22  }   . 
Global Instance Acc_StakingContract·m_minRoundStake : Accessor StakingContract·m_minRoundStake :=  {  acc := ·23  }   . 
Global Instance Acc_StakingContract·m_maxRoundStake : Accessor StakingContract·m_maxRoundStake :=  {  acc := ·24  }   . 
Global Instance Acc_StakingContract·m_lastRoundInterest : Accessor StakingContract·m_lastRoundInterest :=  {  acc := ·25  }   . 
Bind Scope struct_scope with StakingContract·Node  . 
Bind Scope struct_scope with StakingContract·StakeInfo  . 
Instance StakingContract·Node_default : XDefault StakingContract·Node :=  {  
 	 default := StakingContract·NodeC default default  
  }   . 
Instance StakingContract·StakeInfo_default : XDefault StakingContract·StakeInfo :=  {  
 	 default := StakingContract·StakeInfoC default default  
  }   . 
Instance StakingContract_default : XDefault StakingContract :=  {  
 	 default := StakingContractC default default default default default default default default default default default default default default default default default default default default default default default default default default  
  }   . 
End StakingContractClass .


