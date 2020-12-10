Load "Some_more_tools.v".
 
   
Record MultisigWallet_ι_TransactionP  { I64 I32 I8 I256 A I128 I16 C B }  := MultisigWallet_ι_TransactionC  { 
 	MultisigWallet_ι_Transaction_ι_id : I64  ;  
 	MultisigWallet_ι_Transaction_ι_confirmationsMask : I32  ;  
 	MultisigWallet_ι_Transaction_ι_signsRequired : I8  ;  
 	MultisigWallet_ι_Transaction_ι_signsReceived : I8  ;  
 	MultisigWallet_ι_Transaction_ι_creator : I256  ;  
 	MultisigWallet_ι_Transaction_ι_index : I8  ;  
 	MultisigWallet_ι_Transaction_ι_dest : A  ;   (*payable*)  
 	MultisigWallet_ι_Transaction_ι_value : I128  ;  
 	MultisigWallet_ι_Transaction_ι_sendFlags : I16  ;  
 	MultisigWallet_ι_Transaction_ι_payload : C  ;  
 	MultisigWallet_ι_Transaction_ι_bounce : B   
  }  .  
 
 Arguments  MultisigWallet_ι_TransactionC   [   I64 I32 I8 I256 A I128 I16 C B   ]    . 
Record MultisigWallet_ι_LimitP  { I64 I128 I32 I8 I256 }  := MultisigWallet_ι_LimitC  { 
 	MultisigWallet_ι_Limit_ι_id : I64  ;  
 	MultisigWallet_ι_Limit_ι_value : I128  ;  
 	MultisigWallet_ι_Limit_ι_period : I32  ;  
 	MultisigWallet_ι_Limit_ι_required : I8  ;  
 	MultisigWallet_ι_Limit_ι_spent : I256  ;  
 	MultisigWallet_ι_Limit_ι_start : I32  ;  
 	MultisigWallet_ι_Limit_ι_votes : I8  ;  
 	MultisigWallet_ι_Limit_ι_deletionMask : I32   
  }  .  
 
 Arguments  MultisigWallet_ι_LimitC   [   I64 I128 I32 I8 I256   ]    . 
Record MultisigWallet_ι_PendingLimitP  { I256 I8 I32 I64 }  := MultisigWallet_ι_PendingLimitC  { 
 	MultisigWallet_ι_PendingLimit_ι_creator : I256  ;  
 	MultisigWallet_ι_PendingLimit_ι_index : I8  ;  
 	MultisigWallet_ι_PendingLimit_ι_confirmationsMask : I32  ;  
 	MultisigWallet_ι_PendingLimit_ι_signs : I8  ;  
 	MultisigWallet_ι_PendingLimit_ι_parentId : I64  ;  
 	MultisigWallet_ι_PendingLimit_ι_limit : ι_Limit   
  }  .  
 
 Arguments  MultisigWallet_ι_PendingLimitC   [   I256 I8 I32 I64   ]    . 
Record MultisigWallet_ι_UpdateRequestP  { I64 I8 I32 I256 }  := MultisigWallet_ι_UpdateRequestC  { 
 	MultisigWallet_ι_UpdateRequest_ι_id : I64  ;  
 	MultisigWallet_ι_UpdateRequest_ι_index : I8  ;  
 	MultisigWallet_ι_UpdateRequest_ι_signs : I8  ;  
 	MultisigWallet_ι_UpdateRequest_ι_confirmationsMask : I32  ;  
 	MultisigWallet_ι_UpdateRequest_ι_creator : I256  ;  
 	MultisigWallet_ι_UpdateRequest_ι_codeHash : I256  ;  
  	MultisigWallet_ι_UpdateRequest_ι_reqConfirms : I8   
  }  .  
 
 Arguments  MultisigWallet_ι_UpdateRequestC   [   I64 I8 I32 I256   ]    . 
Record MultisigWallet_ι_CustodianInfoP  { I8 I256 }  := MultisigWallet_ι_CustodianInfoC  { 
 	MultisigWallet_ι_CustodianInfo_ι_index : I8  ;  
 	MultisigWallet_ι_CustodianInfo_ι_pubkey : I256   
  }  .  
 
 Arguments  MultisigWallet_ι_CustodianInfoC   [   I8 I256   ]    . 
Record MultisigWallet_ι_PendingLimitInfoP  { I64 }  := MultisigWallet_ι_PendingLimitInfoC  { 
 	MultisigWallet_ι_PendingLimitInfo_ι_id : I64  ;  
 	MultisigWallet_ι_PendingLimitInfo_ι_info : ι_PendingLimit   
  }  .  
 
 Arguments  MultisigWallet_ι_PendingLimitInfoC   [   I64   ]    . 
Record  MultisigWalletP { I128 I32 I8 I64 I I256 Arr }  := MultisigWalletC  { 
 	MultisigWallet_ι_MAX_LIMIT_COUNT : I128  ;   (*constant := 5*) 
 	MultisigWallet_ι_SECONDS_IN_DAY : I32  ;   (*constant := 86400*) 
 	MultisigWallet_ι_MAX_LIMIT_PERIOD : I32  ;   (*constant := 365*) 
 	MultisigWallet_ι_MAX_QUEUED_REQUESTS : I8  ;   (*constant := 5*) 
 	MultisigWallet_ι_MAX_QUEUED_LIMITS_BY_CUSTODIAN : I8  ;   (*constant := 3*) 
 	MultisigWallet_ι_EXPIRATION_TIME : I64  ;   (*constant := 3600*) 
 
 	MultisigWallet_ι_MIN_VALUE : I128  ;   (*constant := 1e6*) 
 	MultisigWallet_ι_MAX_CLEANUP_TXNS : I  ;   (*constant := 40*) 
 	MultisigWallet_ι_FLAG_PAY_FWD_FEE_FROM_BALANCE : I8  ;   (*constant := 1*) 
 	MultisigWallet_ι_FLAG_IGNORE_ERRORS : I8  ;   (*constant := 2*) 
 	MultisigWallet_ι_FLAG_SEND_ALL_REMAINING : I8  ;   (*constant := 128*) 
 	MultisigWallet_ι_m_ownerKey : I256  ; 
 	MultisigWallet_ι_m_requestsMask : I256  ; 
 	MultisigWallet_ι_m_transactions : Arr I64 ι_Transaction  ; 
 	MultisigWallet_ι_m_custodians : Arr I256 I8  ; 
 
 	MultisigWallet_ι_m_limits : Arr I64 ι_Limit  ; 
 
 	MultisigWallet_ι_m_limitRequestsMask : I256  ; 
 	MultisigWallet_ι_m_updateRequests : Arr I64 ι_UpdateRequest  ; 
 	MultisigWallet_ι_m_updateRequestsMask : I32  ; 
 	MultisigWallet_ι_m_requiredVotes : I8  ; 
 	MultisigWallet_ι_m_defaultRequiredConfirmations : I8  
 
 
 
 }   . 
 Arguments MultisigWalletC  [  I128 I32 I8 I64 I I256 Arr  ]   . 
Module MultisigWalletClass (xt: XTypesSig) (sm: StateMonadSig) .
Module SolidityNotations := SolidityNotations.SolidityNotations xt sm.
Import SolidityNotations. 
  
Definition  MultisigWallet_ι_Transaction  := @MultisigWallet_ι_TransactionP  XInteger64 XInteger32 XInteger8 XInteger256 XAddress XInteger128 XInteger16 TvmCell XBool  . 
Definition  MultisigWallet_ι_Limit  := @MultisigWallet_ι_LimitP  XInteger64 XInteger128 XInteger32 XInteger8 XInteger256  . 
Definition  MultisigWallet_ι_PendingLimit  := @MultisigWallet_ι_PendingLimitP  XInteger256 XInteger8 XInteger32 XInteger64  . 
Definition  MultisigWallet_ι_UpdateRequest  := @MultisigWallet_ι_UpdateRequestP  XInteger64 XInteger8 XInteger32 XInteger256  . 
Definition  MultisigWallet_ι_CustodianInfo  := @MultisigWallet_ι_CustodianInfoP  XInteger8 XInteger256  . 
Definition  MultisigWallet_ι_PendingLimitInfo  := @MultisigWallet_ι_PendingLimitInfoP  XInteger64  . 
Definition  MultisigWallet  := @MultisigWalletP  XInteger128 XInteger32 XInteger8 XInteger64 XInteger XInteger256 XArray  . 
Bind Scope struct_scope with MultisigWallet_ι_Transaction  . 
Bind Scope struct_scope with MultisigWallet_ι_Limit  . 
Bind Scope struct_scope with MultisigWallet_ι_PendingLimit  . 
Bind Scope struct_scope with MultisigWallet_ι_UpdateRequest  . 
Bind Scope struct_scope with MultisigWallet_ι_CustodianInfo  . 
Bind Scope struct_scope with MultisigWallet_ι_PendingLimitInfo  . 
Global Instance Struct_MultisigWallet_ι_Transaction : Struct MultisigWallet_ι_Transaction :=  {  
 	 fields :=  [  
 		@existT _ _ _ MultisigWallet_ι_Transaction_ι_id , 
 		@existT _ _ _ MultisigWallet_ι_Transaction_ι_confirmationsMask , 
 		@existT _ _ _ MultisigWallet_ι_Transaction_ι_signsRequired , 
 		@existT _ _ _ MultisigWallet_ι_Transaction_ι_signsReceived , 
 		@existT _ _ _ MultisigWallet_ι_Transaction_ι_creator , 
 		@existT _ _ _ MultisigWallet_ι_Transaction_ι_index , 
 		@existT _ _ _ MultisigWallet_ι_Transaction_ι_dest , 
 		@existT _ _ _ MultisigWallet_ι_Transaction_ι_value , 
 		@existT _ _ _ MultisigWallet_ι_Transaction_ι_sendFlags , 
 		@existT _ _ _ MultisigWallet_ι_Transaction_ι_payload , 
 		@existT _ _ _ MultisigWallet_ι_Transaction_ι_bounce 
 	  ]   ;  
 	 ctor := @MultisigWallet_ι_TransactionC XInteger64 XInteger32 XInteger8 XInteger256 XAddress XInteger128 XInteger16 TvmCell XBool   
  }   . 
Global Instance Acc_MultisigWallet_ι_Transaction_ι_id : Accessor MultisigWallet_ι_Transaction_ι_id :=  {  acc := ·0  }   . 
Global Instance Acc_MultisigWallet_ι_Transaction_ι_confirmationsMask : Accessor MultisigWallet_ι_Transaction_ι_confirmationsMask :=  {  acc := ·1  }   . 
Global Instance Acc_MultisigWallet_ι_Transaction_ι_signsRequired : Accessor MultisigWallet_ι_Transaction_ι_signsRequired :=  {  acc := ·2  }   . 
Global Instance Acc_MultisigWallet_ι_Transaction_ι_signsReceived : Accessor MultisigWallet_ι_Transaction_ι_signsReceived :=  {  acc := ·3  }   . 
Global Instance Acc_MultisigWallet_ι_Transaction_ι_creator : Accessor MultisigWallet_ι_Transaction_ι_creator :=  {  acc := ·4  }   . 
Global Instance Acc_MultisigWallet_ι_Transaction_ι_index : Accessor MultisigWallet_ι_Transaction_ι_index :=  {  acc := ·5  }   . 
Global Instance Acc_MultisigWallet_ι_Transaction_ι_dest : Accessor MultisigWallet_ι_Transaction_ι_dest :=  {  acc := ·6  }   . 
Global Instance Acc_MultisigWallet_ι_Transaction_ι_value : Accessor MultisigWallet_ι_Transaction_ι_value :=  {  acc := ·7  }   . 
Global Instance Acc_MultisigWallet_ι_Transaction_ι_sendFlags : Accessor MultisigWallet_ι_Transaction_ι_sendFlags :=  {  acc := ·8  }   . 
Global Instance Acc_MultisigWallet_ι_Transaction_ι_payload : Accessor MultisigWallet_ι_Transaction_ι_payload :=  {  acc := ·9  }   . 
Global Instance Acc_MultisigWallet_ι_Transaction_ι_bounce : Accessor MultisigWallet_ι_Transaction_ι_bounce :=  {  acc := ·10  }   . 
Global Instance Struct_MultisigWallet_ι_Limit : Struct MultisigWallet_ι_Limit :=  {  
 	 fields :=  [  
 		@existT _ _ _ MultisigWallet_ι_Limit_ι_id , 
 		@existT _ _ _ MultisigWallet_ι_Limit_ι_value , 
 		@existT _ _ _ MultisigWallet_ι_Limit_ι_period , 
 		@existT _ _ _ MultisigWallet_ι_Limit_ι_required , 
 		@existT _ _ _ MultisigWallet_ι_Limit_ι_spent , 
 		@existT _ _ _ MultisigWallet_ι_Limit_ι_start , 
 		@existT _ _ _ MultisigWallet_ι_Limit_ι_votes , 
 		@existT _ _ _ MultisigWallet_ι_Limit_ι_deletionMask 
 	  ]   ;  
 	 ctor := @MultisigWallet_ι_LimitC XInteger64 XInteger128 XInteger32 XInteger8 XInteger256   
  }   . 
Global Instance Acc_MultisigWallet_ι_Limit_ι_id : Accessor MultisigWallet_ι_Limit_ι_id :=  {  acc := ·0  }   . 
Global Instance Acc_MultisigWallet_ι_Limit_ι_value : Accessor MultisigWallet_ι_Limit_ι_value :=  {  acc := ·1  }   . 
Global Instance Acc_MultisigWallet_ι_Limit_ι_period : Accessor MultisigWallet_ι_Limit_ι_period :=  {  acc := ·2  }   . 
Global Instance Acc_MultisigWallet_ι_Limit_ι_required : Accessor MultisigWallet_ι_Limit_ι_required :=  {  acc := ·3  }   . 
Global Instance Acc_MultisigWallet_ι_Limit_ι_spent : Accessor MultisigWallet_ι_Limit_ι_spent :=  {  acc := ·4  }   . 
Global Instance Acc_MultisigWallet_ι_Limit_ι_start : Accessor MultisigWallet_ι_Limit_ι_start :=  {  acc := ·5  }   . 
Global Instance Acc_MultisigWallet_ι_Limit_ι_votes : Accessor MultisigWallet_ι_Limit_ι_votes :=  {  acc := ·6  }   . 
Global Instance Acc_MultisigWallet_ι_Limit_ι_deletionMask : Accessor MultisigWallet_ι_Limit_ι_deletionMask :=  {  acc := ·7  }   . 
Global Instance Struct_MultisigWallet_ι_PendingLimit : Struct MultisigWallet_ι_PendingLimit :=  {  
 	 fields :=  [  
 		@existT _ _ _ MultisigWallet_ι_PendingLimit_ι_creator , 
 		@existT _ _ _ MultisigWallet_ι_PendingLimit_ι_index , 
 		@existT _ _ _ MultisigWallet_ι_PendingLimit_ι_confirmationsMask , 
 		@existT _ _ _ MultisigWallet_ι_PendingLimit_ι_signs , 
 		@existT _ _ _ MultisigWallet_ι_PendingLimit_ι_parentId , 
 		@existT _ _ _ MultisigWallet_ι_PendingLimit_ι_limit 
 	  ]   ;  
 	 ctor := @MultisigWallet_ι_PendingLimitC XInteger256 XInteger8 XInteger32 XInteger64   
  }   . 
Global Instance Acc_MultisigWallet_ι_PendingLimit_ι_creator : Accessor MultisigWallet_ι_PendingLimit_ι_creator :=  {  acc := ·0  }   . 
Global Instance Acc_MultisigWallet_ι_PendingLimit_ι_index : Accessor MultisigWallet_ι_PendingLimit_ι_index :=  {  acc := ·1  }   . 
Global Instance Acc_MultisigWallet_ι_PendingLimit_ι_confirmationsMask : Accessor MultisigWallet_ι_PendingLimit_ι_confirmationsMask :=  {  acc := ·2  }   . 
Global Instance Acc_MultisigWallet_ι_PendingLimit_ι_signs : Accessor MultisigWallet_ι_PendingLimit_ι_signs :=  {  acc := ·3  }   . 
Global Instance Acc_MultisigWallet_ι_PendingLimit_ι_parentId : Accessor MultisigWallet_ι_PendingLimit_ι_parentId :=  {  acc := ·4  }   . 
Global Instance Acc_MultisigWallet_ι_PendingLimit_ι_limit : Accessor MultisigWallet_ι_PendingLimit_ι_limit :=  {  acc := ·5  }   . 
Global Instance Struct_MultisigWallet_ι_UpdateRequest : Struct MultisigWallet_ι_UpdateRequest :=  {  
 	 fields :=  [  
 		@existT _ _ _ MultisigWallet_ι_UpdateRequest_ι_id , 
 		@existT _ _ _ MultisigWallet_ι_UpdateRequest_ι_index , 
 		@existT _ _ _ MultisigWallet_ι_UpdateRequest_ι_signs , 
 		@existT _ _ _ MultisigWallet_ι_UpdateRequest_ι_confirmationsMask , 
 		@existT _ _ _ MultisigWallet_ι_UpdateRequest_ι_creator , 
 		@existT _ _ _ MultisigWallet_ι_UpdateRequest_ι_codeHash , 
 
 		@existT _ _ _ MultisigWallet_ι_UpdateRequest_ι_reqConfirms 
 	  ]   ;  
 	 ctor := @MultisigWallet_ι_UpdateRequestC XInteger64 XInteger8 XInteger32 XInteger256   
  }   . 
Global Instance Acc_MultisigWallet_ι_UpdateRequest_ι_id : Accessor MultisigWallet_ι_UpdateRequest_ι_id :=  {  acc := ·0  }   . 
Global Instance Acc_MultisigWallet_ι_UpdateRequest_ι_index : Accessor MultisigWallet_ι_UpdateRequest_ι_index :=  {  acc := ·1  }   . 
Global Instance Acc_MultisigWallet_ι_UpdateRequest_ι_signs : Accessor MultisigWallet_ι_UpdateRequest_ι_signs :=  {  acc := ·2  }   . 
Global Instance Acc_MultisigWallet_ι_UpdateRequest_ι_confirmationsMask : Accessor MultisigWallet_ι_UpdateRequest_ι_confirmationsMask :=  {  acc := ·3  }   . 
Global Instance Acc_MultisigWallet_ι_UpdateRequest_ι_creator : Accessor MultisigWallet_ι_UpdateRequest_ι_creator :=  {  acc := ·4  }   . 
Global Instance Acc_MultisigWallet_ι_UpdateRequest_ι_codeHash : Accessor MultisigWallet_ι_UpdateRequest_ι_codeHash :=  {  acc := ·5  }   . 
Global Instance Acc_MultisigWallet_ι_UpdateRequest_ι_reqConfirms : Accessor MultisigWallet_ι_UpdateRequest_ι_reqConfirms :=  {  acc := ·6  }   . 
Global Instance Struct_MultisigWallet_ι_CustodianInfo : Struct MultisigWallet_ι_CustodianInfo :=  {  
 	 fields :=  [  
 		@existT _ _ _ MultisigWallet_ι_CustodianInfo_ι_index , 
 		@existT _ _ _ MultisigWallet_ι_CustodianInfo_ι_pubkey 
 	  ]   ;  
 	 ctor := @MultisigWallet_ι_CustodianInfoC XInteger8 XInteger256   
  }   . 
Global Instance Acc_MultisigWallet_ι_CustodianInfo_ι_index : Accessor MultisigWallet_ι_CustodianInfo_ι_index :=  {  acc := ·0  }   . 
Global Instance Acc_MultisigWallet_ι_CustodianInfo_ι_pubkey : Accessor MultisigWallet_ι_CustodianInfo_ι_pubkey :=  {  acc := ·1  }   . 
Global Instance Struct_MultisigWallet_ι_PendingLimitInfo : Struct MultisigWallet_ι_PendingLimitInfo :=  {  
 	 fields :=  [  
 		@existT _ _ _ MultisigWallet_ι_PendingLimitInfo_ι_id , 
 		@existT _ _ _ MultisigWallet_ι_PendingLimitInfo_ι_info 
 	  ]   ;  
 	 ctor := @MultisigWallet_ι_PendingLimitInfoC XInteger64   
  }   . 
Global Instance Acc_MultisigWallet_ι_PendingLimitInfo_ι_id : Accessor MultisigWallet_ι_PendingLimitInfo_ι_id :=  {  acc := ·0  }   . 
Global Instance Acc_MultisigWallet_ι_PendingLimitInfo_ι_info : Accessor MultisigWallet_ι_PendingLimitInfo_ι_info :=  {  acc := ·1  }   . 
Global Instance Struct_MultisigWallet : Struct MultisigWallet :=  { 
 	fields :=  [ 
 		@existT _ _ _ MultisigWallet_ι_MAX_LIMIT_COUNT , 
 		@existT _ _ _ MultisigWallet_ι_SECONDS_IN_DAY , 
 		@existT _ _ _ MultisigWallet_ι_MAX_LIMIT_PERIOD , 
 		@existT _ _ _ MultisigWallet_ι_MAX_QUEUED_REQUESTS , 
 		@existT _ _ _ MultisigWallet_ι_MAX_QUEUED_LIMITS_BY_CUSTODIAN , 
 		@existT _ _ _ MultisigWallet_ι_EXPIRATION_TIME , 
 
 		@existT _ _ _ MultisigWallet_ι_MIN_VALUE , 
 		@existT _ _ _ MultisigWallet_ι_MAX_CLEANUP_TXNS , 
 		@existT _ _ _ MultisigWallet_ι_FLAG_PAY_FWD_FEE_FROM_BALANCE , 
 		@existT _ _ _ MultisigWallet_ι_FLAG_IGNORE_ERRORS , 
 		@existT _ _ _ MultisigWallet_ι_FLAG_SEND_ALL_REMAINING , 
 		@existT _ _ _ MultisigWallet_ι_m_ownerKey , 
 		@existT _ _ _ MultisigWallet_ι_m_requestsMask , 
 		@existT _ _ _ MultisigWallet_ι_m_transactions , 
 		@existT _ _ _ MultisigWallet_ι_m_custodians , 
 
 		@existT _ _ _ MultisigWallet_ι_m_limits , 
 
 		@existT _ _ _ MultisigWallet_ι_m_limitRequestsMask , 
 		@existT _ _ _ MultisigWallet_ι_m_updateRequests , 
 		@existT _ _ _ MultisigWallet_ι_m_updateRequestsMask , 
 		@existT _ _ _ MultisigWallet_ι_m_requiredVotes , 
 		@existT _ _ _ MultisigWallet_ι_m_defaultRequiredConfirmations 
 
 
 
 	 ]   ;  
 	ctor := @MultisigWalletC XInteger128 XInteger32 XInteger8 XInteger64 XInteger XInteger256 XArray
 }   . 
Global Instance Acc_MultisigWallet_ι_MAX_LIMIT_COUNT : Accessor MultisigWallet_ι_MAX_LIMIT_COUNT :=  {  acc := ·0  }   . 
Global Instance Acc_MultisigWallet_ι_SECONDS_IN_DAY : Accessor MultisigWallet_ι_SECONDS_IN_DAY :=  {  acc := ·1  }   . 
Global Instance Acc_MultisigWallet_ι_MAX_LIMIT_PERIOD : Accessor MultisigWallet_ι_MAX_LIMIT_PERIOD :=  {  acc := ·2  }   . 
Global Instance Acc_MultisigWallet_ι_MAX_QUEUED_REQUESTS : Accessor MultisigWallet_ι_MAX_QUEUED_REQUESTS :=  {  acc := ·3  }   . 
Global Instance Acc_MultisigWallet_ι_MAX_QUEUED_LIMITS_BY_CUSTODIAN : Accessor MultisigWallet_ι_MAX_QUEUED_LIMITS_BY_CUSTODIAN :=  {  acc := ·4  }   . 
Global Instance Acc_MultisigWallet_ι_EXPIRATION_TIME : Accessor MultisigWallet_ι_EXPIRATION_TIME :=  {  acc := ·5  }   . 
Global Instance Acc_MultisigWallet_ι_MIN_VALUE : Accessor MultisigWallet_ι_MIN_VALUE :=  {  acc := ·6  }   . 
Global Instance Acc_MultisigWallet_ι_MAX_CLEANUP_TXNS : Accessor MultisigWallet_ι_MAX_CLEANUP_TXNS :=  {  acc := ·7  }   . 
Global Instance Acc_MultisigWallet_ι_FLAG_PAY_FWD_FEE_FROM_BALANCE : Accessor MultisigWallet_ι_FLAG_PAY_FWD_FEE_FROM_BALANCE :=  {  acc := ·8  }   . 
Global Instance Acc_MultisigWallet_ι_FLAG_IGNORE_ERRORS : Accessor MultisigWallet_ι_FLAG_IGNORE_ERRORS :=  {  acc := ·9  }   . 
Global Instance Acc_MultisigWallet_ι_FLAG_SEND_ALL_REMAINING : Accessor MultisigWallet_ι_FLAG_SEND_ALL_REMAINING :=  {  acc := ·10  }   . 
Global Instance Acc_MultisigWallet_ι_m_ownerKey : Accessor MultisigWallet_ι_m_ownerKey :=  {  acc := ·11  }   . 
Global Instance Acc_MultisigWallet_ι_m_requestsMask : Accessor MultisigWallet_ι_m_requestsMask :=  {  acc := ·12  }   . 
Global Instance Acc_MultisigWallet_ι_m_transactions : Accessor MultisigWallet_ι_m_transactions :=  {  acc := ·13  }   . 
Global Instance Acc_MultisigWallet_ι_m_custodians : Accessor MultisigWallet_ι_m_custodians :=  {  acc := ·14  }   . 
Global Instance Acc_MultisigWallet_ι_m_limits : Accessor MultisigWallet_ι_m_limits :=  {  acc := ·15  }   . 
Global Instance Acc_MultisigWallet_ι_m_limitRequestsMask : Accessor MultisigWallet_ι_m_limitRequestsMask :=  {  acc := ·16  }   . 
Global Instance Acc_MultisigWallet_ι_m_updateRequests : Accessor MultisigWallet_ι_m_updateRequests :=  {  acc := ·17  }   . 
Global Instance Acc_MultisigWallet_ι_m_updateRequestsMask : Accessor MultisigWallet_ι_m_updateRequestsMask :=  {  acc := ·18  }   . 
Global Instance Acc_MultisigWallet_ι_m_requiredVotes : Accessor MultisigWallet_ι_m_requiredVotes :=  {  acc := ·19  }   . 
Global Instance Acc_MultisigWallet_ι_m_defaultRequiredConfirmations : Accessor MultisigWallet_ι_m_defaultRequiredConfirmations :=  {  acc := ·20  }   . 
Instance MultisigWallet_ι_Transaction_default : XDefault MultisigWallet_ι_Transaction :=  {  
 	 default := MultisigWallet_ι_TransactionC default default default default default default default default default default default  
  }   . 
Instance MultisigWallet_ι_Limit_default : XDefault MultisigWallet_ι_Limit :=  {  
 	 default := MultisigWallet_ι_LimitC default default default default default default default default  
  }   . 
Instance MultisigWallet_ι_PendingLimit_default : XDefault MultisigWallet_ι_PendingLimit :=  {  
 	 default := MultisigWallet_ι_PendingLimitC default default default default default default  
  }   . 
Instance MultisigWallet_ι_UpdateRequest_default : XDefault MultisigWallet_ι_UpdateRequest :=  {  
 	 default := MultisigWallet_ι_UpdateRequestC default default default default default default default  
  }   . 
Instance MultisigWallet_ι_CustodianInfo_default : XDefault MultisigWallet_ι_CustodianInfo :=  {  
 	 default := MultisigWallet_ι_CustodianInfoC default default  
  }   . 
Instance MultisigWallet_ι_PendingLimitInfo_default : XDefault MultisigWallet_ι_PendingLimitInfo :=  {  
 	 default := MultisigWallet_ι_PendingLimitInfoC default default  
  }   . 
Instance MultisigWallet_default : XDefault MultisigWallet :=  {  
 	 default := MultisigWalletC default default default default default default default default default default default default default default default default default default default default default  
  }   . 
End MultisigWalletClass .


