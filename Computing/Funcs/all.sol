pragma solidity >=0.6.0;

interface IElector {
    /// @dev Allows node to become validator candidate
    function elector_process_new_stake(
        uint64 queryId,
        uint256 validatorKey,
        uint32 stakeAt,
        uint32 maxFactor,
        uint256 adnlAddr,
        bytes signature
    ) external functionID(0x4E73744B);

    /// @dev Allows to get back node's stake
    function elector_recover_stake(uint64 queryId) external functionID(0x47657424);
}pragma solidity >=0.6.0;
pragma AbiHeader expire;
pragma AbiHeader time;

interface IParticipant {
    /// @dev Send a notification message to stakeholder with info about its stake and reward in round.
    /// @param roundId Id of completed round.
    /// @param reward Amount of stakeholder reward for round in nanograms
    /// @param stake Size of stake in completed round in nanograms
    /// @param reinvest True - if stake is automatically moved to next round.
    /// @param fee Size of commission for sending this notification message.
    /// @param reason Code that defines the origin of notification: lookup `Round completion statuses`
    function receiveRewardStake(
        uint32 roundId,
        uint64 reward,
        uint64 stake,
        bool reinvest,
        uint64 fee,
        uint8 reason) external;

    /// @dev Send a message with status code and certain value to stakeholder as a result of staking operation.
    /// @param errcode Error code of operation.
    /// @param comment Additional value for certain error code.
    function receiveAnswer(uint32 errcode, uint64 comment) external;
}

contract Participant is IParticipant {
    function receiveRewardStake(
        uint32 roundId,
        uint64 reward,
        uint64 stake,
        bool reinvest,
        uint64 fee,
        uint8 reason) external override
    { }

    function receiveAnswer(uint32 errcode, uint64 comment) external override { }
}pragma solidity >=0.5.0;

interface IProxy {
    function process_new_stake(
        uint64 queryId,
        uint256 validatorKey,
        uint32 stakeAt,
        uint32 maxFactor,
        uint256 adnlAddr,
        bytes signature
    ) external;

    function recover_stake(uint64 queryId) external;
}pragma solidity >=0.5.0;

interface IStaking {
    function receiveConfirmation(uint64 queryId, uint32 comment) external;
    function receiveReturnedStake(uint64 queryId, uint32 comment) external returns (uint64 _queryId, uint32 _comment);
    function acceptRecoveredStake(uint64 queryId) external;
    function ticktock() external;
}pragma solidity >0.6.0;
pragma experimental ABIEncoderV2;
pragma AbiHeader expire;
pragma AbiHeader time;

contract Stakeholder {
    function sendTransaction(
        address dest,
        uint64 value,
        bool bounce,
        uint16 flags,
        TvmCell payload) public view
    {
        require(msg.pubkey() == tvm.pubkey(), 100);
        tvm.accept();
        dest.transfer(value, bounce, flags, payload);
    }

    receive() external virtual {}
    fallback() external virtual {}
}pragma solidity >=0.6.0;

import "IProxy.sol";

contract AcceptBase {
    modifier onlyOwner {
        require(msg.pubkey() == tvm.pubkey(), 300);
        _;
    }

    constructor() public onlyOwner {
        tvm.accept();
    }
}

contract OwnerBase {
    // The pool owner
    struct Owner {
        // Owner's contract address.
        address addr;
        // Owner reward.
        uint64 reward;
    }

    // Staking pool owner.
    Owner m_owner;

    constructor(address poolOwnerAddr) internal {
        m_owner = Owner(poolOwnerAddr, 0);
    }

    modifier onlyOwnerContract {
        require(msg.sender == m_owner.addr, 106);
        _;
    }

    /// @dev Allows to withdraw the Owner's reward
    function withdrawOwnerReward(uint64 amount) public onlyOwnerContract {
        require(amount <= m_owner.reward, 105);
        m_owner.reward -= amount;
        m_owner.addr.transfer(amount, true, 3);
    }

    function _increaseOwnerReward(uint64 ownerReward) internal inline {
        m_owner.reward += ownerReward;
    }
}

contract ElectorBase {

    // Number of nanograms attached to recover_stake message to elector contract.
    uint64 constant RECOVER_STAKE_MSG_VALUE = 1e9;

    // Elector contract address.
    address m_elector;

    // Request for elections from node wallet.
    struct Request {
        // Random query id.
        uint64 queryId;
        // Node's public key that will be used as validator key if node will win elections.
        uint256 validatorKey;
        // current election id.
        uint32 stakeAt;
        // Node's stake factor.
        uint32 maxFactor;
        // Node's address in adnl overlay network.
        uint256 adnlAddr;
        // Ed25519 signature of above values.
        bytes signature;
    }

    constructor(address electorAddr) internal {
        m_elector = electorAddr;
    }

    modifier onlyElector {
        require(msg.sender == m_elector, 107);
        _;
    }

    // A method to request back stakes (part of stakes) after unsuccessful elections in the last but 1 round
    function _recoverStakes() internal {
        IProxy(m_elector).recover_stake.value(RECOVER_STAKE_MSG_VALUE)(0);
    }

    function _recoverStakeRewards() internal {
        IProxy(m_elector).recover_stake.value(RECOVER_STAKE_MSG_VALUE)(1);
    }

    function _recoverPendingRoundStakes(uint32 pendingId) internal {
        IProxy(m_elector).recover_stake.value(RECOVER_STAKE_MSG_VALUE)(pendingId);
    }

    function _runForElection(Request req, uint64 nodeStake) internal {
        // send stake + 1 gram  + 2*0.01 gram (proxy fee),
        // 1 gram will be used by Elector to return confirmation back to staking contract.
        IProxy(m_elector).process_new_stake.value(nodeStake + 1e9 + 2*1e7)(
            req.queryId,
            req.validatorKey,
            req.stakeAt,
            req.maxFactor,
            req.adnlAddr,
            req.signature
        );
    }

}

contract ElectionParams {

    // Structure for tvm_config_param34
    struct ValidatorDescr73 {
        uint8 validator_addr73;
        uint32 ed25519_pubkey;
        uint256 pubkey;
        uint64 weight;
        uint256 adnl_addr;
    }

    // Current active elections identifier (the same as returned by active_election_id method of elector contract).
    // Unixtime when the next GVS is installed
    uint32 m_electAt;

    // Describes when elections should be started before new validator set will be installed. Interval in seconds.
    uint32 m_beginBefore;

    // Describes when elections should be finished before new validator set will be installed. Interval in seconds.
    uint32 m_endBefore;

    // Describes period when validator set is active (in seconds).
    uint32 m_electedFor;

    // Describes interval after validation period when validator's stakes cannot be recovered (in seconds).
    uint32 m_heldFor;

    constructor(
        uint32 electionId,
        uint32 beginBefore,
        uint32 endBefore,
        uint32 heldFor,
        uint32 electedFor
    ) internal {
        if (electionId != 0) {
            m_electAt = electionId;
        } else {
            m_electAt = _getNextElectionId();
        }
        bool ok;
        (m_electedFor, m_beginBefore, m_endBefore, m_heldFor, ok) = tvm.configParam(15);
        if (!ok) {
            m_beginBefore = beginBefore;
            m_endBefore = endBefore;
            m_electedFor = electedFor;
            m_heldFor = heldFor;
        }
    }

    /// @dev Returns period in seconds of stake freezing.
    function _getFreezingPeriod() internal view inline returns (uint32) {
        return m_electedFor + m_heldFor;
    }

    /// @dev Allows to get period of staking round
    function _getStakingPeriod() internal view returns (uint32) {
        // here m_electedFor is pooling period
        return m_electedFor + m_beginBefore + _getFreezingPeriod();
    }

    function _isRoundUnfrozen(uint32 electAt) internal view inline returns (bool) {
        return now > (electAt + _getFreezingPeriod());
    }

    ///@dev Returns next election id
    function _getNextElectionId() private inline view returns (uint32) {
        uint32 utime_until;
        bool ok;
        (, , utime_until, , , , , ok) = tvm.configParam(34);
        if (!ok) {
            // WARNING: use next 2 lines in DEBUG mode
            uint32 offset = ((uint32(now) - (m_electAt - m_beginBefore)) / m_electedFor + 1) * m_electedFor;
            utime_until = m_electAt + offset;
        }
        return utime_until;
    }

    function _getElectionsStart() internal inline view returns (uint32) {
        return m_electAt - m_beginBefore;
    }

    function _setAndGetNextElectAt() internal inline returns (uint32) {
        uint32 nextElectAt = _getNextElectionId();
        if (now >= nextElectAt - m_beginBefore) {
            nextElectAt += m_electedFor;
        }
        m_electAt = nextElectAt;
        return nextElectAt;
    }

    function _getElectAt() internal inline view returns (uint32) {
        return m_electAt;
    }

    function _isElectionOver(uint32 currentElectAt) internal inline view returns (bool) {
        return now >= (currentElectAt - m_endBefore);
    }

}

contract StakeholderBase {

    // Describes contract who deposit stakes in staking pool
    struct Stakeholder {
        // Total stake (including vesting) of a stakeholder in all rounds and unused stake
        // TODO delete this. It's superfluous value. Can be gotten from m_rounds mapping. Store just count of round
        // in which he take a part to delete stakeholder from `m_stakeholders`
        uint64 totalStake;
        // Total unused stake that isn't invested in any round.
        // Unused stake can be withdrawn at any time.
        uint64 unusedStake;
        // Flag whether to reinvest stakes and rewards.
        bool reinvest;
        // Gross reward from completed rounds (don't included in totalStake, totalStake includes net reward).
        uint64 grossReward;
        // Unix time in seconds of last payment
        uint64 lastPaymentUnixTime;
        // Period in seconds after which `periodPayment` nanotons are unlocked
        uint32 withdrawalPeriod;
        // Amount of nanotons which are unlocked after `withdrawalPeriod`
        uint64 periodPayment;
        // address of creator of vesting
        address vestingOwner;
    }

    // Dictionary of stakeholders for active rounds.
    mapping (address => Stakeholder) m_stakeholders;

    function _haveVesting(Stakeholder stakeholder) internal inline pure returns (bool) {
        return stakeholder.periodPayment != 0;
    }

    function _stakeholderSetVesting(Stakeholder stakeholder, uint64 stake, uint32 withdrawalPeriod,
                                    uint64 periodPayment, address vestingOwner) internal inline returns (Stakeholder) {
        stakeholder.totalStake += stake;
        stakeholder.lastPaymentUnixTime = uint64(now);
        stakeholder.withdrawalPeriod = withdrawalPeriod;
        stakeholder.periodPayment = periodPayment;
        stakeholder.vestingOwner = vestingOwner;
        return stakeholder;
    }

    function _stakeholderExists(address addr) internal view inline returns (bool) {
        return m_stakeholders.exists(addr);
    }

    function _getStakeholder(address addr) internal view inline returns (Stakeholder) {
        return m_stakeholders[addr];
    }

    function _stakeholderFetch(address addr) internal view inline returns (bool, Stakeholder) {
        return m_stakeholders.fetch(addr);
    }

    function _setOrDeleteStakeholder(address addr, Stakeholder stakeholder) internal inline {
        if (stakeholder.totalStake == 0)
            delete m_stakeholders[addr];
        else
            m_stakeholders[addr] = stakeholder;
    }

    function _stakeholderUpdateStake(address addr, uint64 totalStake, bool reinvest) internal inline {
        Stakeholder user = m_stakeholders[addr];
        user.reinvest = reinvest;
        user.totalStake += totalStake;
        m_stakeholders[addr] = user;
    }

    function _stakeholderUpdateStake2(Stakeholder stakeholder, uint64 totalStake, bool reinvest) internal inline
    returns (Stakeholder) {
        stakeholder.reinvest = reinvest;
        stakeholder.totalStake += totalStake;
        return stakeholder;
    }

    function _stakeholderRemoveStake(address addr, uint64 removedStake, uint64 unusedStake) internal inline {
        Stakeholder stakeholder = m_stakeholders[addr];
        stakeholder.totalStake -= removedStake;
        stakeholder.unusedStake -= unusedStake;

        // if stakeholder has no stakes in other rounds, delete it from dictionary
        if (stakeholder.totalStake == 0) {
            // NOTE: totalStake include unusedStake. So if totalStake==0 than unusedStake==0
            delete m_stakeholders[addr];
        } else {
            m_stakeholders[addr] = stakeholder;
        }
    }

    function _stakeholderIncreaseTotalAndUnused(Stakeholder stakeholder, uint64 deltaTotal, uint64 deltaUnused
    ) internal inline returns (Stakeholder) {
        stakeholder.totalStake += deltaTotal;
        stakeholder.unusedStake += deltaUnused;
        return stakeholder;
    }

    function _stakeholderDecreaseTotalAndUnused(Stakeholder stakeholder, uint64 deltaTotal, uint64 deltaUnused
    ) internal inline returns (Stakeholder) {
        stakeholder.totalStake -= deltaTotal;
        stakeholder.unusedStake -= deltaUnused;
        return stakeholder;
    }

    function _stakeholderSetReinvest(address addr, bool flag) internal inline {
        m_stakeholders[addr].reinvest = flag;
    }

    function _stakeholderSetReinvest2(Stakeholder stakeholder, bool flag) internal inline returns (Stakeholder) {
        stakeholder.reinvest = flag;
        return stakeholder;
    }

    function _stakeholderUpdateGrossReward(Stakeholder stakeholder, uint64 reward) internal inline returns (Stakeholder) {
        stakeholder.grossReward += reward;
        return stakeholder;
    }

    function _stakeholderUpdateTotalStake(Stakeholder stakeholder, uint64 newStake, uint64 oldStake) internal inline
        returns (Stakeholder) {

        if (newStake >= oldStake)
            stakeholder.totalStake += newStake - oldStake;
        else
            stakeholder.totalStake -= oldStake - newStake;
        return stakeholder;
    }

    function _stakeholderUpdateUnusedStake(address addr, uint64 add, uint64 remove) internal inline {
        // ALWAYS add==0 or remove==0. See usage of function _stakeholderUpdateUnusedStake
        // TODO add two inline function for inc and dec unusedStake
        m_stakeholders[addr].unusedStake = (m_stakeholders[addr].unusedStake + add) - remove;
    }

    function _stakeholderIncreaseUnusedStake(Stakeholder stakeholder, uint64 delta) internal inline returns (Stakeholder) {
        stakeholder.unusedStake += delta;
        return stakeholder;
    }

    function _stakeholderDecreaseUnusedStake(Stakeholder stakeholder, uint64 delta) internal inline returns (Stakeholder) {
        stakeholder.unusedStake -= delta;
        return stakeholder;
    }

    function _stakeholderResetVesting(Stakeholder stakeholder) internal inline returns (Stakeholder) {
        stakeholder.lastPaymentUnixTime = 0;
        stakeholder.withdrawalPeriod = 0;
        stakeholder.periodPayment = 0;
        stakeholder.vestingOwner = address(0);
        return stakeholder;
    }

    function _stakeholderUpdateLastPaymentTime(Stakeholder stakeholder, uint64 periodQty)
    internal inline returns (Stakeholder) {
        stakeholder.lastPaymentUnixTime += periodQty * stakeholder.withdrawalPeriod;
        return stakeholder;
    }
}

pragma solidity >0.5.0;
pragma experimental ABIEncoderV2;
pragma AbiHeader expire;
import "./Stakeholder.sol";
import "./IStaking.sol";

interface ITimer {
    function setTimer(uint timer) external;
}

contract StakingOwner is Stakeholder {
    // Helper structure to represent contract address.
    struct Address {
        address addr;
    }

    uint constant TICKTOCK_FEE = 1e9;
    uint constant TIMER_FEE = 1e9;
    // Actual staking pool contract address.
    address m_stakingPool;
    // Array of old (closed) staking contract addresses.
    Address[] m_poolHistory;
    // Timer contract address.
    address m_timer;
    // Timer timeout.
    uint m_timeout;

    constructor(address pool) public acceptOnlyOwner {
        m_stakingPool = pool;
    }

    modifier acceptOnlyOwner {
        require(msg.pubkey() == tvm.pubkey(), 101);
        tvm.accept();
        _;
    }

    /*
        public methods
    */

    function updateStakingPoolAddress(address addr) public acceptOnlyOwner {
        m_poolHistory.push(Address(m_stakingPool));
        m_stakingPool = addr;
    }

    /*
     * Timer functions
     */

    /// @notice Allows to set timer contract address and init timer.
    /// @param timer Address of a timer contract.
    /// Can be called only by off-chain app with owner keys.
    function initTimer(address timer, uint period) public acceptOnlyOwner {
        m_timer = timer;
        m_timeout = period;
        _settimer(timer, period);
    }

    /// @notice Allows to init timer sending request to Timer contract.
    /// @param timer Address of a timer contract.
    function _settimer(address timer, uint period) private inline {
        ITimer(timer).setTimer.value(TIMER_FEE)(period);
    }

    /// @notice Timer callback function.
    function onTimer() public {
        address timer = m_timer;
        uint period = m_timeout;
        if (msg.sender == timer && period > 0) {
            IStaking(m_stakingPool).ticktock.value(TICKTOCK_FEE)();
            _settimer(timer, period);
        }
    }

    /*
        get methods
    */

    function getStakingPoolAddress() public view returns (address addr) {
        addr = m_stakingPool;
    }

    function getHistory() public view returns (Address[] list) {
        list = m_poolHistory;
    }

    /*
     * Set code
     */

    function upgrade(TvmCell newcode) public acceptOnlyOwner {
        tvm.commit();
        tvm.setcode(newcode);
        tvm.setCurrentCode(newcode);
        onCodeUpgrade();
    }

    function onCodeUpgrade() private {}

    receive() external override {}
    fallback() external override {}
}
pragma solidity >=0.6.0;
pragma experimental ABIEncoderV2;
import "IElector.sol";
import "IStaking.sol";
import "IProxy.sol";

contract StakingProxyContract is IProxy {

    uint64 constant PROXY_FEE = 1e7; //0.01GR

    address m_staking;
    address m_elector;

    constructor(address staking, address elector) public {
        require(msg.pubkey() == tvm.pubkey(), 100);
        tvm.accept();
        m_staking = staking;
        m_elector = elector;
    }

    modifier onlyElector {
        require(msg.sender == m_elector, 101);
        _;
    }

    modifier onlyStaking {
        require(msg.sender == m_staking, 102);
        _;
    }
    /*
        Proxy functions called by Staking contract.
    */

    /// @dev Allows to send node request to run for validator elections
    function process_new_stake(
        uint64 queryId,
        uint256 validatorKey,
        uint32 stakeAt,
        uint32 maxFactor,
        uint256 adnlAddr,
        bytes signature
    ) external override onlyStaking {
        IElector(m_elector).elector_process_new_stake.value(msg.value - PROXY_FEE)(
            queryId, validatorKey, stakeAt, maxFactor, adnlAddr, signature
        );
    }

    /// @dev Allows to recover node stake
    function recover_stake(uint64 queryId) public override onlyStaking {
        IElector(m_elector).elector_recover_stake.value(msg.value - PROXY_FEE)(queryId);
    }

    /*
     * Functions called by Elector contract
     */

    /// @dev Elector answer from process_new_stake in case of success.
    function receive_confirmation(uint64 queryId, uint32 comment) public functionID(0xF374484C) onlyElector {
        // Elector contract always send 1GR
        IStaking(m_staking).receiveConfirmation.value(msg.value - PROXY_FEE)(queryId, comment);
    }

    /// @dev Elector answer from process_new_stake in case of error.
    function receive_returned_stake(uint64 queryId, uint32 comment) public functionID(0xEE6F454C) onlyElector {
        IStaking(m_staking).receiveReturnedStake.value(msg.value - PROXY_FEE)(queryId, comment);
    }

    /// @dev Elector answer from recover_stake in case of success.
    function accept_recovered_stake(uint64 queryId) public functionID(0xF96F7324) onlyElector {
        IStaking(m_staking).acceptRecoveredStake.value(msg.value - PROXY_FEE)(queryId);
    }

    receive() external {}
    fallback() external {}
}pragma solidity >=0.6.0;

contract RoundsBase {

    // Round steps:
    // pooling step, round accepts stakes
    uint8 constant STEP_POOLING = 0;
    // 'waiting for election requests' from nodes
    uint8 constant STEP_WAITING_REQUESTS = 1;
    // sending election requests to elector contract
    uint8 constant STEP_ELECTIONS = 2;
    // checking election results
    uint8 constant STEP_WAITING_ELECTION_RESULTS = 3;
    // waiting node stake unfreeze
    uint8 constant STEP_WAITING_UNFREEZE = 4;
    // round is closed
    uint8 constant STEP_COMPLETED = 5;
    // round is pending to complete
    uint8 constant STEP_COMPLETING = 6;

    // Round completion statuses. Filled when round is completed.
    uint8 constant ROUND_UNDEFINED = 0;
    uint8 constant ROUND_RECEIVED_REWARD = 7;
    uint8 constant ROUND_POOL_CLOSED = 1;
    uint8 constant ROUND_MISSED_ELECTIONS = 2;
    uint8 constant ROUND_NOT_ENOUGH_TOTAL_STAKE = 3;
    uint8 constant ROUND_NODE_STAKE_TOO_SMALL = 4;
    uint8 constant ROUND_STAKE_REJECTED = 5;
    uint8 constant ROUND_LOST_ELECTIONS = 6;

    struct StakeValue {
        uint64 simple;
        uint64 vesting;
    }

    // Investment round information
    struct Round {
        // Same as electAt
        uint32 id;
        // Round step
        uint8 step;
        // Number of stakeholders in round.
        uint32 participantQty;
        // Round total stake
        uint64 stake;
        // Round rewards
        uint64 rewards;
        // Unused stake cut-off by elector
        uint64 unused;
        // Status code why round is completed.
        uint8 completionStatus;
        // Unixtime when round is created.
        uint32 start;
        // Unixtime when round is completed.
        uint32 end;
        // stakeholder's stakes in round
        mapping(address => StakeValue) stakes;
    }

    // Used in get-methods for returning round information
    struct RoundInfo {
        // Round id.
        uint32 id;
        // Unixtime when round is created.
        uint32 start;
        // Unixtime when round is completed.
        uint32 end;
        // Round current step.
        uint8 step;
        // See `Round completion statuses`.
        uint8 completionStatus;
        // Round total stake.
        uint64 stake;
        // Number of stakeholders in round.
        uint32 stakeholderCount;
        // Round rewards.
        uint64 rewards;
    }

    // Set of active rounds. 4 rounds can be active simultaneously.
    mapping(uint64 => Round) m_rounds;

    // Index of first round in m_rounds mapping. After deleting of completed round this value is incremented.
    uint64 m_startIdx;

    // Number of active rounds. Can be from 0 to 4.
    uint8 m_roundsCount;

    // List of rounds that are not completed in one transaction and that
    // are waiting for completion.
    mapping(uint32 => Round) m_pendingRounds;

    /// This helper function is used in public getter function
    function _getRoundsInfo() internal view inline returns (RoundInfo[] infos) {
        (uint64 index, Round round, bool ok) = m_rounds.min();
        while (ok) {
            infos.push(RoundInfo(round.id, round.start, round.end, round.step,
                round.completionStatus, round.stake, round.participantQty, round.rewards));
            (index, round, ok) = m_rounds.next(index);
        }
    }

    /// This helper function is used in public getter function
    function _getPendingRoundsInfo() internal view inline returns (RoundInfo[] infos) {
        (uint32 key, Round round, bool ok) = m_pendingRounds.min();
        while (ok) {
            infos.push(RoundInfo(round.id, round.start, round.end, round.step,
                round.completionStatus, round.stake, round.participantQty, round.rewards));
            (key, round, ok) = m_pendingRounds.next(key);
        }
    }

    function _getLastRoundIdx() private view inline returns (uint64) {
        return m_startIdx + m_roundsCount - 1;
    }

    function _addNewPoolingRound(uint32 validationStart, uint32 validationPeriod) internal inline {
        m_rounds[m_startIdx + m_roundsCount] = Round({
            id: validationStart, step: STEP_POOLING, participantQty: 0, stake: 0,
            rewards: 0, unused: 0, completionStatus: ROUND_UNDEFINED,
            start: uint32(now), end: validationStart + validationPeriod
        });
        m_roundsCount++;
    }

    function _getRoundsCount() internal view inline returns (uint8) {
        return m_roundsCount;
    }

    function _removeOldestRound() internal inline returns (Round) {
        (, Round round) = m_rounds.delMin();
        m_startIdx++;
        m_roundsCount--;
        return round;
    }

    function _getOldestRound() internal view inline returns (Round) {
        return m_rounds[m_startIdx];
    }

    function _setOldestRound(Round round) internal inline {
        m_rounds[m_startIdx] = round;
    }

    function _getLastRound() internal view inline returns (Round) {
        // TODO why not m_rounds[_getLastRoundIdx()]? See _getOldestRound and _getPenultimateRound
        (bool exists, Round round) = m_rounds.fetch(_getLastRoundIdx());
        require(exists, 200);
        return round;
    }

    function _setLastRound(Round round) internal inline {
        m_rounds[_getLastRoundIdx()] = round;
    }

    function _getPenultimateRound() internal view inline returns (Round) {
        return m_rounds[_getLastRoundIdx() - 1];
    }

    function _setPenultimateRound(Round round) internal inline {
        m_rounds[_getLastRoundIdx() - 1] = round;
    }

    function _roundAddStakeAndVesting(
        Round round,
        address addr,
        uint64 stake,
        uint64 vestingStake
    ) internal inline returns (Round)  {
        uint64 totalStake = stake + vestingStake;
        if (totalStake == 0)
            return round;
        if (!round.stakes.exists(addr)) {
            round.participantQty++;
        }
        round.stake += totalStake;
        StakeValue sv = round.stakes[addr];
        sv.simple += stake;
        sv.vesting += vestingStake; // NOTE: One stakeholder can have only on vesting
        round.stakes[addr] = sv;
        return round;
    }

    /// Walk through the rounds and transfer stake from source to destination.
    /// return Count of transferred tokens
    function _roundMoveStakes(
        address source,
        address destination,
        uint64 targetAmount
    ) internal inline returns (uint64) {
        (uint64 roundId, Round round, bool ok) = m_rounds.min();
        uint64 transferred = 0;
        while (ok && targetAmount != 0) {
            if (round.step != STEP_COMPLETED && round.step != STEP_COMPLETING) {
                uint64 currentTransferred;
                (m_rounds[roundId], currentTransferred) = _roundMoveStake(round, source, destination, targetAmount);
                targetAmount -= currentTransferred;
                transferred += currentTransferred;
            }
            (roundId, round, ok) = m_rounds.next(roundId);
        }
        return transferred;
    }

    /// this function move stake a size of `amount` from `source` to `destination` in the `round`
    /// return count of transferred tokens (amount can be cut off)
    function _roundMoveStake(
        Round round,
        address source,
        address destination,
        uint64 amount
    ) internal inline returns (Round, uint64) {
        (bool exists, StakeValue sourceStake) = round.stakes.fetch(source);
        if (!exists)
            return (round, 0);
        uint64 newSourceStake;
        uint64 deltaDestinationStake;
        if (sourceStake.simple >= amount) {
            newSourceStake = sourceStake.simple - amount;
            deltaDestinationStake = amount;
        } else {
            newSourceStake = 0;
            deltaDestinationStake = sourceStake.simple;
        }

        if (newSourceStake == 0 && round.stakes[source].vesting == 0) {
            --round.participantQty;
            delete round.stakes[source];
        } else {
            round.stakes[source].simple = newSourceStake;
        }

        if (!round.stakes.exists(destination))
            round.participantQty++;
        // TODO what if deltaDestinationStake < minStake
        round.stakes[destination].simple += deltaDestinationStake;

        return (round, deltaDestinationStake);
    }

    function _addPendingRound(Round round) internal inline {
        m_pendingRounds[round.id] = round;
    }

    function _removePendingRound(uint32 pendingId) internal inline
        returns (bool exists, Round round) {
        (exists, round) = m_pendingRounds.fetch(pendingId);
        if (exists) {
            delete m_pendingRounds[pendingId];
        }
    }

    function _roundFetchPendingRound(uint32 pendingId) internal inline returns(bool, Round) {
        return m_pendingRounds.fetch(pendingId);
    }

    function _setOrDeletePendingRound(Round round) internal inline {
        if (round.step == STEP_COMPLETED) {
            delete m_pendingRounds[round.id];
        } else {
            m_pendingRounds[round.id] = round;
        }
    }

    function _deletePendingRound(uint32 id) internal inline {
        delete m_pendingRounds[id];
    }

    function getTotalStake(StakeValue stakes) internal inline returns (uint64) {
        return stakes.simple + stakes.vesting;
    }

    function arePendingRoundsEmpty() internal inline returns (bool) {
        return m_pendingRounds.empty();
    }
    
    function _fetchOldestPendingRound() internal inline  returns (uint32, Round, bool) {
        return m_pendingRounds.min();
    }
}
pragma solidity >=0.6.0;
pragma experimental ABIEncoderV2;
pragma AbiHeader expire;
pragma AbiHeader time;
pragma ignoreIntOverflow; // TODO comment this and run test_suite!!!;
import "IStaking.sol";
import "IParticipant.sol";
import "Staking-Common.sol";
import "Staking-Rounds.sol";

contract StakingContract is AcceptBase, OwnerBase, ElectorBase, ElectionParams, StakeholderBase, RoundsBase, IStaking {

    /*
     * Structures
     */

    // Node structure.
    struct Node {
        // Node wallet address.
        address wallet;
        // Node's stake factor.
        uint32 factor;      // TODO: seems to be unused?
        // Node's stake in elections.
        uint64 stake; // TODO delete this
    }

    /*
     * Constants
     */

    // Fraction (pct) of nominators rewards in totalRewards.
    uint constant NOM_FRACTION = 70;
    // Fraction (pct) of node owner rewards in totalRewards.
    uint constant NODE_FRACTION = 25;
    // Fee for withdrawal of stake.
    uint64 constant REMOVE_STAKE_FEE = 3e7;
    // Fee for transferring stake.
    uint64 constant TRANSFER_STAKE_FEE = 1e8;
    // Fee for adding stake (or vesting).
    uint64 constant ADD_STAKE_FEE = 3e8;
    // Fee for pause of stake investment.
    uint64 constant PAUSE_STAKE_FEE = 3e7;
    // Fee for continue of stake investment.
    uint64 constant CONTINUE_STAKE_FEE = 3e7;
    // Fee for calling setReinvest.
    uint64 constant SET_REINVEST_FEE = 3e7;
    // Fee for sending notification message when rounds completes.
    uint64 constant NOTIFY_FEE = 3e6;
    // min stake for elections 10001 Gram
    uint constant MIN_VAL_STAKE = 10001000000000;
    // Number of nominator stakes reinvesting in 1 transaction.
    uint8 constant MAX_MSGS_PER_TR = 40;
    // Minimal required percentage of node wallet stake in total round stake.
    uint8 constant NODE_WALLET_MIN_STAKE = 20;
    // Number of nanograms to cover inbound message value error when elector
    // returns unused stake.
    uint64 constant ROUND_UP_VALUE = 1e9;
    // Nanograms attached to answer message to allow a receiver contract
    // to be executed.
    uint64 constant ANSWER_MSG_FEE = 3e6;
    // max value that can store money type (uint64)
    uint64 constant MAX_MONEY_VALUE = 0xFFFF_FFFF_FFFF_FFFF;

    // Status codes for messages sending back to stakeholders as result of
    // operations (add/remove/continue stake):
    uint8 constant STATUS_SUCCESS                                        =  0;
    uint8 constant STATUS_STAKE_TOO_SMALL                                =  1;
    uint8 constant STATUS_NO_ACTIVE_ROUNDS                               =  2;
    uint8 constant STATUS_POOL_CLOSED                                    =  3;
    uint8 constant STATUS_ROUND_STAKE_LIMIT                              =  4;
    uint8 constant STATUS_MSG_VAL_TOO_SMALL                              =  5;
    uint8 constant STATUS_NO_STAKE                                       =  6;
    //uint8 constant                                                     =  7;
    uint8 constant STATUS_NO_TRANSFER_WHILE_PENDING_ROUND                =  8;
    uint8 constant STATUS_STAKEHOLDER_HAVE_ALREADY_VESTING               =  9;
    uint8 constant STATUS_WITHDRAWAL_PERIOD_GREATER_TOTAL_PERIOD         = 10;
    uint8 constant STATUS_TOTAL_PERIOD_MORE_100YEARS                     = 11;
    uint8 constant STATUS_WITHDRAWAL_PERIOD_IS_ZERO                      = 12;
    uint8 constant STATUS_TOTAL_PERIOD_IS_NOT_DIVED_BY_WITHDRAWAL_PERIOD = 13;
    uint8 constant STATUS_PERIOD_PAYMENT_IS_ZERO                         = 14;

    /*
     * Global variables
     */

    // Indicates that pool is closed. Closed pool doesn't accept stakes from other contracts.
    bool m_poolClosed;

    // Requests for different rounds.
    mapping(uint32 => Request) m_requests; // roundId -> request

    // Validator candidate
    Node m_node;

    // Min stake accepted to the pool in nGram (for gas efficiency reasons): 10 grams is recommended.
    uint64 m_minStake;

    // Minimum and maximum round total stake
    uint64 m_minRoundStake;
    uint64 m_maxRoundStake;

    // Staking annual interest, this value is recalculated after each round with reward.
    uint64 m_lastRoundInterest;

    /*
     * Events
     */

    // Event emitted when elections started and signed node requests are required from all node wallets in node pool.
    event stakeSigningRequested(uint32 electId);

    // Event emitted in terminator() function
    event stakingPoolClosed();

    /*
      EXCEPTION CODES:
      100 - message sender is not owner;
      101 - message sender is not stakeholder contract;
      105 - not enough funds;
      106 - message sender is not owner contract;
      107 - message sender is not elector contract;
      108 - function cannot be called by external message;
      110 - invalid confirmation from elector;
      111 - request from node has invalid electionId;
      112 - request from node already received in current round;
      113 - msg sender is not in node pool;
      114 - staking pool is closed;
      116 - stakeholder with such address does not exist;
      117 - maximum round stake is reached;
      118 - round does not accept requests at this step;
      119 - invalid target for stake transfer or add vesting;
      120 - message sender is not dePool (this is not self call)
      121 - there is no pending rounds;
      122 - pending round is just created;
    */

    // TODO: add named constants for exception codes above!

    modifier onlyInternalMessage {
        // allow call only from other contracts.
        require(msg.sender != address(0), 108);
        _;
    }

    function _addNewRoundAndUpdateRounds() private inline {
        // calculate last active round accepting stakes
        // append it to the list of rounds

        _addNewPoolingRound(_setAndGetNextElectAt(), _getFreezingPeriod());

        // implement a queue of 4 rounds to minimize storage
        if (_getRoundsCount() > 4) {
            Round removingRound = _removeOldestRound();
            delete m_requests[removingRound.id];
            if (removingRound.step == STEP_WAITING_ELECTION_RESULTS) {
                // if last ticktock was more then 'staking period' ago then oldest
                // round can be in such step, need to recover its stake from elector contract.
                _addPendingRound(removingRound);
                _recoverPendingRoundStakes(removingRound.id);
            }
        }

        if (_getRoundsCount() > 1) {
            _setPenultimateRound(_requestStakesSigning(_getPenultimateRound()));
        }
    }

    function _checkPenultimateRound() private inline returns (bool) {
        Round lb1Round = _getPenultimateRound();
        if (now > lb1Round.id) {
            if (lb1Round.step < STEP_ELECTIONS) {
                // we don't run elections, time is over
                _setPenultimateRound(_completeRoundAndSetCompletionStatus(lb1Round, ROUND_MISSED_ELECTIONS));
                return true;
            }
            if (lb1Round.step < STEP_WAITING_ELECTION_RESULTS) {
                // after elections end in 'last but one' round,
                // request and return/reinvest stakes after unsuccessful elections
                _recoverStakes();
                lb1Round.step = STEP_WAITING_ELECTION_RESULTS;
                _setPenultimateRound(lb1Round);
                return true;
            }
        }
        return false;
    }

    function _checkOldestRound() private inline returns (bool) {
        Round oldestRound = _getOldestRound();
        if (_isRoundUnfrozen(oldestRound.id)) {
            if (oldestRound.step == STEP_WAITING_ELECTION_RESULTS) {
                // after the lb3 round end
                // request and return/reinvest stakes and rewards after the round end
                _recoverStakeRewards();
                oldestRound.step = STEP_WAITING_UNFREEZE;
                _setOldestRound(oldestRound);
                return true;
            }
            // [Q] Can oldestRound be at another step?
            //      yep, it can be already completed (step 5) if it missed elections
            //      (not enough stake, or it didn't receive node signature).
            // TODO: it can be a bug if round will be in STEP_ELECTIONS step.
        }
        return false;
    }

    /// @notice Helper function to return unused grams back to caller contract.
    function _returnGrams() private pure {
        msg.sender.transfer(0, true, 64);
    }

    /// @dev helper function for calculation round interest.
    /// Returns last calculated value. If no rewards in round, returns 0.
    function _calcLastRoundInterest(uint64 totalStake, uint64 rewards) private pure inline returns (uint64) {
        return (totalStake != 0) ? uint64((rewards * 100 * 1e9) / totalStake) : 0;
    }

    /// @dev Generates a message with error code and parameter sent back to caller contract.
    /// @param errcode Error code.
    /// @param amount Value of nanograms to send back.
    /// @param comment Additional parameter according to error code.
    function _returnAnswer(uint32 errcode, uint64 amount, uint64 comment) private {
        // TODO why 64? why Not 64 + 2?
        IParticipant(msg.sender).receiveAnswer{value:amount, flag: (amount == 0 ? 64 : 3)}(errcode, comment);
    }

    function _returnError(uint32 errcode, uint64 comment) private inline {
        _returnAnswer(errcode, 0, comment);
    }

    /// @dev Send a message with success status to stakeholder meaning that operation is completed successfully.
    /// Used in addStake.
    /// @param fee Operation fee value that was consumed for operation.
    function _returnConfirmation(uint64 fee) private inline {
        _returnAnswer(STATUS_SUCCESS, ANSWER_MSG_FEE, fee);
    }

    /// @dev Transfer new stake and part of unused stake to last round.
    /// @param addr Stakeholder address.
    /// @param unusedStake Amount of unused stake to move to last round.
    /// @param newStake Amount new stake to invest into last round.
    /// @param reinvest Reinvestment flag.
    function _investStake(address addr, uint64 unusedStake, uint64 newStake, bool reinvest) private returns (bool) {
        Stakeholder stakeholder = _getStakeholder(addr);
        // If desired unusedStake is exceed real stakeholder's unused value than cut off desired unusedStake.
        unusedStake = tvm.min(unusedStake, stakeholder.unusedStake);

        uint64 investStake = unusedStake + newStake;
        Round round = _getLastRound();
        // TODO BUG? what if fromUnused == true AND round.stake + investStake - unusedStake <= m_maxRoundStake (we can take only part of unused money)
        // For example: it's called from addStake(). User want add little stake and set reinvest == true (but we add all unused stake and condition below is false)
        if (round.stake + investStake > m_maxRoundStake) {
            return false;
        }

        _setLastRound(_roundAddStakeAndVesting(round, addr, investStake, 0));

        stakeholder =_stakeholderDecreaseUnusedStake(stakeholder, unusedStake);
        if (newStake > 0) {
            stakeholder = _stakeholderUpdateStake2(stakeholder, newStake, reinvest);
        } else {
            stakeholder = _stakeholderSetReinvest2(stakeholder, reinvest);
        }
        _setOrDeleteStakeholder(addr, stakeholder);

        return true;
    }

    /* ---------- Election requests ---------- */

    // A method to send stakes to the Elector contract in the last but 1 active round
    function _requestStakesSigning(Round round) private inline returns (Round) {
        uint64 roundStake = round.stake;
        uint32 currentElectAt = round.id;

        // check that round total stake is greater or equal to minimum stake
        bool roundStakeCheck = roundStake >= m_minRoundStake;
        // and node wallet made a necessary minimal stake in round
        bool nodeStakeCheck  = getTotalStake(round.stakes[m_node.wallet]) >= (m_minRoundStake * NODE_WALLET_MIN_STAKE) / 100;

        bool canParticipate = !_isElectionOver(currentElectAt) && roundStakeCheck && nodeStakeCheck;
        if (canParticipate) {
            m_node.stake = roundStake;
            emit stakeSigningRequested(currentElectAt);

            // try to send stakes to elector if we already received request from node
            (bool exists, Request request) = m_requests.fetch(currentElectAt);
            if (exists) {
                round.step = STEP_ELECTIONS;
                _runForElection(request, roundStake);
            } else {
                round.step = STEP_WAITING_REQUESTS;
            }
        } else {
            // otherwise node cannot participate in elections,
            // complete round
            uint8 completionStatus = !roundStakeCheck ? ROUND_NOT_ENOUGH_TOTAL_STAKE : ROUND_NODE_STAKE_TOO_SMALL;
            round = _completeRoundAndSetCompletionStatus(round, completionStatus);
        }
        return round;
    }

    function _addRequest(uint32 stakeAt, Request request) private inline {
        // check that node should send request only once.
        require(!m_requests.exists(stakeAt), 112);

        // save request
        m_requests[stakeAt] = request;
    }

    /*
     * ---------- Private functions for sending and receiving stakes ----------------
    */

    function _acceptPendingRoundStake(uint32 pendingId) private {
        (bool exists, Round round) = _removePendingRound(pendingId);
        if (exists) {
            // TODO: why the returning round is not saved to m_pendingRounds?
            // It can be a bug. Test this case.
            _completeRoundAndSetCompletionStatus(round, ROUND_RECEIVED_REWARD);
        }
    }

    // Reinvest or return unused stakes
    function _acceptUnusedStake() private {
        // last but 1 active round
        Round lb1round = _getPenultimateRound();
        // if elector returns all stake it means that we lose elections
        // otherwise elector returns unused cut-off part of node stake.
        if (msg.value >= lb1round.stake) {
            _setPenultimateRound(_completeRoundAndSetCompletionStatus(lb1round, ROUND_LOST_ELECTIONS));
            // all stake is returned - we lost the election, because round stake is too small,
            // increase a minimum round stake on 1/4
            m_minRoundStake += m_minRoundStake / 4;
            // TODO BUG? check that (m_minRoundStake < m_maxRoundStake) or (сoef * m_minRoundStake < m_maxRoundStake) where сoef > 1
            // if not than increase m_maxRoundStake. And see another branch of current if-else
        } else {
            // only part of round stake is returned - we won the election,
            // but round stake is cut-off by elector,
            // optimize a minimum round stake

            lb1round.unused = uint64(msg.value);

                // TODO: this value does not seem to be saved anywhere
                //  > yep, this is a bug, case with unused stake is not tested.
                //  > Please add a test exposing this bug before fixing it!

            m_minRoundStake = lb1round.stake - lb1round.unused + ROUND_UP_VALUE;
        }
    }

    // Reinvest or return stakes and rewards
    function _acceptRewardStake() private {
        Round oldestRound = _getOldestRound();
        uint64 roundStake = oldestRound.stake - oldestRound.unused;

        uint64 totalReward = 0;
        if (uint64(msg.value) >= roundStake) {
            totalReward = uint64(msg.value) - roundStake;
        }
        uint64 roundReward = uint64((totalReward * NOM_FRACTION) / 100);
        uint64 ownerReward = uint64((totalReward * NODE_FRACTION) / 100);
        _increaseOwnerReward(ownerReward);
        oldestRound.rewards = roundReward;

        m_lastRoundInterest = _calcLastRoundInterest(roundStake, roundReward);

        _setOldestRound(_completeRoundAndSetCompletionStatus(oldestRound, ROUND_RECEIVED_REWARD));
    }

    /*
     *  Round functions
     */

    /// @dev Allows to complete round, return or reinvest its stakes to last round.
    /// If there are more then MAX_MSGS_PER_TR stakeholders in round, round switches to pending step
    /// and completion is split into several transactions. The contract send several 'completePendingRoundChunk'
    /// messages to itself to continue returning or reinvesting stakes.
    function _completeRound(Round completedRound, uint8 chunkSize) private returns (Round) {
        completedRound.step = STEP_COMPLETING;
        completedRound.end = uint32(now);
        _setOrDeletePendingRound(completedRound);

        tvm.accept();
        tvm.commit();

        completedRound = _completePendingRound(completedRound, chunkSize);
        _setOrDeletePendingRound(completedRound);

        delete completedRound.stakes;
        return completedRound;
    }

    function _completePendingRound(Round pendingRound, uint8 chunkSize) private returns (Round) {
        if (pendingRound.participantQty > chunkSize) {
            // send loopback messages for postponed processing

            for (uint i = 0; i < pendingRound.participantQty; i+= chunkSize) {
                this.completePendingRoundChunk.value(1e7)(pendingRound.id, chunkSize);
            }
        } else {
            // process immediately

            pendingRound = _returnOrReinvest(pendingRound, chunkSize);
        }
        return pendingRound;
    }

    function _completeRoundAndSetCompletionStatus(Round round, uint8 completionStatus) private inline returns (Round) {
        round.completionStatus = completionStatus;
        return _completeRound(round, MAX_MSGS_PER_TR);
    }

    /// @notice Helper inline function to calculate stake with reward and fees
    function _getStakeAndFeeAndUpdateMinStakeIfNeeded(
        uint64 stake,
        uint64 reward,
        uint64 roundStake,
        uint64 roundRewards
    ) private inline returns (uint64 _newStake, uint64 _fee) {

        // check if fee is less than stakeholder reward
        if (NOTIFY_FEE < stake + reward) {
            if (reward != 0 && NOTIFY_FEE > reward) {
                // increase min stake, its reward now is less then reinvest fee
                // math proportion: NOTIFY_FEE / m_minStake = roundRewards / roundStake
                m_minStake = uint64((roundStake * NOTIFY_FEE) / roundRewards);
                // TODO upd this var only in function _returnOrReinvest, because this var are used in function _returnOrReinvestForStakeholder
            }
            return (stake + reward - NOTIFY_FEE, NOTIFY_FEE);
        } else {
            return (0, stake + reward);
        }
    }

    function getNewStakeAndFees(uint64 roundRewards, uint64 roundStake, uint64 stake) internal inline
        returns(uint64, uint64, uint64) {

        if (stake == 0) {
            return (0, 0, 0);
        }
        uint64 reward = (roundStake != 0) ? uint64(roundRewards * stake / roundStake) : 0;
        (uint64 stakeAndReward, uint64 fee) = _getStakeAndFeeAndUpdateMinStakeIfNeeded(stake, reward, roundStake, roundRewards);
        return (reward, stakeAndReward, fee);
    }

    /// @param completedRound Completed round by some any reason (elector return reward, loose elections, etc.)
    /// @param lastRound Round that is in pooling state
    /// @param addr Stakeholder address from completed round
    /// @param stake Stakeholder stake in completed round
    function _returnOrReinvestForStakeholder(
        Round completedRound,
        Round lastRound,
        address addr,
        StakeValue stake
    ) private inline returns (Round) {
        // TODO maybe here we must subtract not only NOTIFY_FEE but also ADD_STAKE_FEE? Note ADD_STAKE_FEE == 100 * NOTIFY_FEE

        uint64 roundRewards = completedRound.rewards;
        uint64 roundStake = completedRound.stake;
        Stakeholder stakeholder = _getStakeholder(addr);
        bool reinvest = stakeholder.reinvest;

        (uint64 stakeReward, uint64 newStake, uint64 stakeFee) =
            getNewStakeAndFees(roundRewards, roundStake, stake.simple);
        (uint64 vestingReward, uint64 vestingAndReward, uint64 vestingFee) =
            getNewStakeAndFees(roundRewards, roundStake, stake.vesting);
        uint64 pureVestingReward = vestingAndReward >= stake.vesting? vestingAndReward - stake.vesting : 0;
        uint64 newVesting = tvm.min(vestingAndReward - pureVestingReward, stake.vesting);

        stakeholder = _stakeholderUpdateGrossReward(stakeholder, stakeReward + vestingReward);
        stakeholder = _stakeholderUpdateTotalStake(stakeholder, newStake + vestingAndReward,
                                                   stake.simple + stake.vesting);

        uint64 withdrawalVesting = 0; // Amount of locked vesting that can be unlocked.
        if (stake.vesting != 0) {
            uint64 periodQty = (uint64(now) - stakeholder.lastPaymentUnixTime) / stakeholder.withdrawalPeriod;
            withdrawalVesting = tvm.min(periodQty * stakeholder.periodPayment, newVesting);
            newVesting -= withdrawalVesting;
            stakeholder = _stakeholderUpdateLastPaymentTime(stakeholder, periodQty);
            if (newVesting < m_minStake) {
                stakeholder = _stakeholderIncreaseUnusedStake(stakeholder, newVesting);
                stakeholder = _stakeholderResetVesting(stakeholder);
                newVesting = 0;
            }
        }

        newStake += withdrawalVesting + pureVestingReward;
        // if (newStake < m_minStake) { // TODO add all unused money if reinvest is on??? No, i think we should not invest all funds from unused part if reinvest is on.
        //     stakeholder = _stakeholderIncreaseUnusedStake(stakeholder, newStake);
        //     newStake = 0;
        // }

        uint64 attachedValue;
        if (m_poolClosed) {
            attachedValue = newStake + stakeholder.unusedStake;
            stakeholder = _stakeholderDecreaseTotalAndUnused(stakeholder,
                                                             newStake + newVesting + stakeholder.unusedStake,
                                                             stakeholder.unusedStake);
            if (newVesting != 0 && stakeholder.vestingOwner != address(0)) {
                // return rest of vesting stake to owner of vesting
                stakeholder.vestingOwner.transfer({value: newVesting, flag: 3});
            }
            stakeholder = _stakeholderResetVesting(stakeholder);
        } else {
            attachedValue = 1;
            if (reinvest) {
                // reinvest stakeholder's stake in last round
                // NOTE: newStake + newVesting != 0 is checked in called function
                lastRound = _roundAddStakeAndVesting(lastRound, addr, newStake, newVesting);
            } else {
                // don't reinvest but stay stake as available
                stakeholder = _stakeholderIncreaseUnusedStake(stakeholder, newStake);
                // NOTE:  newVesting != 0 is checked in called function
                lastRound = _roundAddStakeAndVesting(lastRound, addr, 0, newVesting);
            }
        }

        _setOrDeleteStakeholder(addr, stakeholder);
        IParticipant(addr).receiveRewardStake{value: attachedValue, flag: 3}(
            completedRound.id,
            stakeReward + vestingReward,
            newStake + newVesting, // TODO new stake // TODO add vesting params separate
            reinvest,
            stakeFee + vestingFee,
            completedRound.completionStatus
        );

        return lastRound;
    }

    /// @dev Internal routine for reinvesting stakes of completed round to last round.
    /// Iterates over stakes of completed round no more then MAX_MSGS_PER_TR times.
    /// Sets round step to STEP_COMPLETING if there are more stakes then MAX_MSGS_PER_TR.
    /// Otherwise sets step to STEP_COMPLETED.
    /// @param completedRound Round structure that should be completed.
    function _returnOrReinvest(Round completedRound, uint8 chunkSize) private returns (Round) {

        // get stakes of completed round
        mapping(address => StakeValue) stakes = completedRound.stakes;

        // last active round accepting stakes
        Round lastRound = _getLastRound();

        uint sentMsgs = 0;
        while (!stakes.empty() && sentMsgs < chunkSize) {
            sentMsgs++;
            (address addr, StakeValue stake) = stakes.delMin();
            lastRound = _returnOrReinvestForStakeholder(completedRound, lastRound, addr, stake);
        }

        if (completedRound.id != lastRound.id) {
            // NOTE: if we call terminate() than completedRound == lastRound. In function _returnOrReinvestForStakeholder
            // we don't update lastRound. In function terminate() we set completedRound in the last round
            _setLastRound(lastRound);
        }

        completedRound.step = stakes.empty() ? STEP_COMPLETED : STEP_COMPLETING;
        completedRound.stakes = stakes;
        return completedRound;
    }

    ////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
    //// Public Functions

    /// @dev Constructor with the elector address, the 1st node in node pool, the owner and elections parameters.
    constructor(
        address electorAddr,
        address poolOwnerAddr,
        uint32 electionId,
        address nodeWallet,
        uint32 beginBefore,
        uint32 endBefore,
        uint32 heldFor,
        uint32 electedFor,
        uint64 minStake,
        uint64 minRoundStake,
        uint64 maxRoundStake
        )
        OwnerBase(poolOwnerAddr)
        ElectorBase(electorAddr)
        ElectionParams(electionId, beginBefore, endBefore, heldFor, electedFor)
        public
    {
        m_minStake = minStake;
        m_minRoundStake = minRoundStake;
        m_maxRoundStake = maxRoundStake;

        m_poolClosed = false;

        m_node = Node(nodeWallet, 3 * 65536, 0);
    }

    function _getStakeAndSendErrorIfNeeded() private returns (uint64 stake, bool ok) {
        ok = true;

        uint64 msgValue = uint64(msg.value);
        // TODO: check that msg.currencies is empty

        // send stake back if stake is less then minimal
        uint64 minRequiredValue = m_minStake + ADD_STAKE_FEE;
        if (msgValue < minRequiredValue) {
            _returnError(STATUS_STAKE_TOO_SMALL, minRequiredValue);
            return (0, false);
        }
        // or if pool is closed
        if (m_poolClosed) {
            _returnError(STATUS_POOL_CLOSED, 0);
            return (0, false);
        }
        // or no rounds in contract
        if (_getRoundsCount() == 0) {
            _returnError(STATUS_NO_ACTIVE_ROUNDS, 0);
            return (0, false);
        }
        return (msgValue - ADD_STAKE_FEE, true);
    }

    /// @dev A method to add a stakeholder or add stake by an existing stakeholder in the last active round.
    function addStake(bool reinvest) public onlyInternalMessage {
        // TODO don't accept new stakes (vesting and etc.) if we have at least one pending round
        (uint64 stake, bool ok) = _getStakeAndSendErrorIfNeeded();
        if (!ok) {
            return ;
        }

        if (!_investStake(msg.sender, reinvest? MAX_MONEY_VALUE : 0, stake, reinvest)) {
            Round round = _getLastRound();
            return _returnError(STATUS_ROUND_STAKE_LIMIT, m_maxRoundStake - round.stake);
        }

        _returnConfirmation(ADD_STAKE_FEE);
    }

    /// @dev A method to add the vesting for stakeholder in the last active round.
    /// @param dest Contract address for vesting
    /// @param totalPeriod Total period of vesting in seconds
    /// @param withdrawalPeriod The period in seconds after which you can withdraw money
    function addVesting(address dest, uint32 withdrawalPeriod, uint32 totalPeriod) public {
        require(dest.isStdAddrWithoutAnyCast(),  119);
        if (dest == address(0)) {
            dest = msg.sender;
        }

        (uint64 stake, bool ok) = _getStakeAndSendErrorIfNeeded();
        if (!ok) {
            return ;
        }

        Round round = _getLastRound();
        if (round.stake + stake > m_maxRoundStake) {
            return _returnError(STATUS_ROUND_STAKE_LIMIT, m_maxRoundStake - round.stake);
        }

        if (withdrawalPeriod > totalPeriod) {
            return _returnError(STATUS_WITHDRAWAL_PERIOD_GREATER_TOTAL_PERIOD, 0);
        }

        if (totalPeriod >= 100 * (365 days)) { // 100 years
            return _returnError(STATUS_TOTAL_PERIOD_MORE_100YEARS, 0);
        }

        if (withdrawalPeriod == 0) {
            return _returnError(STATUS_WITHDRAWAL_PERIOD_IS_ZERO, 0);
        }

        if (totalPeriod % withdrawalPeriod != 0) {
            return _returnError(STATUS_TOTAL_PERIOD_IS_NOT_DIVED_BY_WITHDRAWAL_PERIOD, 0);
        }

        Stakeholder stakeholder = _getStakeholder(dest);
        if (_haveVesting(stakeholder)) {
            return _returnError(STATUS_STAKEHOLDER_HAVE_ALREADY_VESTING, 0);
        }

        uint64 periodPayment = uint64(uint(stake) * withdrawalPeriod / totalPeriod);
        if (periodPayment == 0) {
            return _returnError(STATUS_PERIOD_PAYMENT_IS_ZERO, 0);
        }
        stakeholder = _stakeholderSetVesting(stakeholder, stake, withdrawalPeriod, periodPayment, msg.sender);
        _setOrDeleteStakeholder(dest, stakeholder);
        _setLastRound(_roundAddStakeAndVesting(round, dest, 0, stake));
        _returnConfirmation(ADD_STAKE_FEE);
    }

    /// @dev Allows a stakeholder to remove its stake (before the deadline for elections start).
    /// If removing stake is bigger that nominator's stake in last active round,
    /// then return all nominator's stake otherwise return requested stake minus removing fee.
    function removeStake(uint64 stake) public onlyInternalMessage {
        // throw if removing amount is less than fee
        if (msg.value < REMOVE_STAKE_FEE) {
            _returnError(STATUS_MSG_VAL_TOO_SMALL, REMOVE_STAKE_FEE);
            return;
        }

        Stakeholder member = _getStakeholder(msg.sender);
        uint64 removedStake = tvm.min(stake, member.unusedStake);

        // TODO gas opt: use _stakeholderRemoveStake2
        _stakeholderRemoveStake(msg.sender, removedStake, removedStake);

        msg.sender.transfer(removedStake, true, 3);
    }

    /// @dev Invest unused stakeholder's stake into last round.
    /// @param amount Part of unused stake in nanograms to invest.
    /// Use 0 to invest all unused funds.
    /// @param reinvest True - enables automatic reinvestment to next round.
    /// False - funds are invested only in one next round and then moved to unused part.
    function continueStake(uint64 amount, bool reinvest) public onlyInternalMessage {
        // TODO return error if amount==0 and user don't have unused money???
        if (msg.value < CONTINUE_STAKE_FEE) {
            return _returnError(STATUS_MSG_VAL_TOO_SMALL, CONTINUE_STAKE_FEE);
        }

        if (!_stakeholderExists(msg.sender)) {
            return _returnError(STATUS_NO_STAKE, 0);
        }

        if (!_investStake(msg.sender, amount == 0? MAX_MONEY_VALUE : amount, 0, reinvest)) {
            Round round = _getLastRound();
            return _returnError(STATUS_ROUND_STAKE_LIMIT, m_maxRoundStake - round.stake);
        }

        // TODO check that depool is not closed

        _returnConfirmation(CONTINUE_STAKE_FEE);
    }

    /// @dev A method to update the reinvest flag in a specified round
    function setReinvest(bool flag) public onlyInternalMessage {
        // allow call only from other contracts.
        address sender = msg.sender;
        // TODO check that depool is not closed
        require(_stakeholderExists(sender), 101);
        _stakeholderSetReinvest(sender, flag);
    }

    /// @dev Transfer stake or part of it to another stakeholder.
    /// @param destination Target stakeholder address.
    /// @param amount Part of stake in nanograms to transfer.
    /// Use 0 to transfer the whole stake.
    function transferStake(address destination, uint64 amount) public onlyInternalMessage {
        address sender = msg.sender;
        // allow call only from a stakeholder.
        (bool exists, Stakeholder donor) = _stakeholderFetch(sender);
        require(exists, 101);
        // target address should be set.
        require(destination.isStdAddrWithoutAnyCast() && !destination.isStdZero(),  119);

        // return error if msg value doesn't cover the fee
        if (msg.value < TRANSFER_STAKE_FEE) {
            return _returnError(STATUS_MSG_VAL_TOO_SMALL, TRANSFER_STAKE_FEE);
        }

        // return error if have any pending rounds
        if (!arePendingRoundsEmpty()) {
            return _returnError(STATUS_NO_TRANSFER_WHILE_PENDING_ROUND, 0);
        }

        // return error if pool is closed
        if (m_poolClosed) {
            return _returnError(STATUS_POOL_CLOSED, 0);
        }

        if (amount == 0) {
            amount = MAX_MONEY_VALUE;
        }

        Stakeholder receiver = _getStakeholder(destination);
        uint64 transferredStake = _roundMoveStakes(sender, destination, amount);
        uint64 transferredUnused = tvm.min(amount - transferredStake, donor.unusedStake);
        uint64 transferred = transferredStake + transferredUnused;

        donor = _stakeholderDecreaseTotalAndUnused(donor, transferred, transferredUnused);
        receiver = _stakeholderIncreaseTotalAndUnused(receiver, transferred, transferredUnused);

        _setOrDeleteStakeholder(sender, donor);
        _setOrDeleteStakeholder(destination, receiver);

        _returnConfirmation(TRANSFER_STAKE_FEE);
    }

    //id = 0x4e73744b
    function processNewStake(
        uint64 queryId,
        uint256 validatorKey,
        uint32 stakeAt,
        uint32 maxFactor,
        uint256 adnlAddr,
        bytes signature
    ) public functionID(0x4E73744B) {

        // check that sender contract is a controlled node wallet.
        require(m_node.wallet == msg.sender, 113);

        Request request = Request(queryId, validatorKey, stakeAt, maxFactor, adnlAddr, signature);
        // TODO check that stakeAt is not from past. stakeAt >= _getElectAt() - stakingPeriod
        _addRequest(stakeAt, request);

        if (stakeAt == _getElectAt()) {

            // if request is for last round which is always in pooling step, then exit,
            // because round is not ready to accept election requests;
            // in one of the next ticktocks last round will be switched to next step and become 'last but one' round
            // and at that time requests will be sent to Elector.

        } else {

            // TODO: not sure about this require()...
            require(_getRoundsCount() >= 2, 111);

            // get last but one round
            Round round = _getPenultimateRound();

            // check that it is ready for accepting election requests.
            require(round.step == STEP_WAITING_REQUESTS, 118);

            // received election Id must be equal to last but one round or last round id.
            require(stakeAt == round.id, 111);

            // check that all node wallets from validator pool send requests and then send them to elector contracts
            _runForElection(request, m_node.stake);

            round.step = STEP_ELECTIONS;
            _setPenultimateRound(round);
        }

        _returnGrams();
    }

    /// @dev Updates round states, sends election requests and accepts rewards.
    function ticktock() public override onlyInternalMessage {
        bool electionsStarted = now >= _getElectionsStart();

        if (electionsStarted) {
            // 'electAt' round is in stage after elections start,
            // stop accepting nominator stakes and prepare node stakes for sending to Elector,
            // also create new round.
            _addNewRoundAndUpdateRounds();
        } else  if (_getRoundsCount() < 2) {         // electionsStarted == false
            if (_getRoundsCount() == 0)
                _addNewRoundAndUpdateRounds();
        } else if (_checkPenultimateRound()) {
        } else if (_checkOldestRound()) {
        }

        _returnGrams();
    }

    /// @dev Allows other contracts to force completion of pending round
    /// @param doCompleteOneChunk - If True then only part of pending stakes will be completed, not all round.
    /// If False - all round will be completed.
    /// @param chunkSize Number of stakes that depool must reinvest or return in 1 transaction.
    function forceCompletePendingRound(bool doCompleteOneChunk, uint8 chunkSize) public onlyInternalMessage {
        (, Round round, bool ok) = _fetchOldestPendingRound();
        require(ok, 121); // at least one pending round must exists
        // we should force pending rounds created more than hour ago. If round is still pending it means
        // it failed to complete automatically.
        require(round.end + 1 hours < now, 122);
        tvm.accept();
        if (doCompleteOneChunk) {
            round = _returnOrReinvest(round, chunkSize);
        } else {
            round = _completePendingRound(round, chunkSize);
        }
        _setOrDeletePendingRound(round);
    }

    /// @dev Allows to return or reinvest part of stakes from last completed round.
    /// @param roundId Id of completed round.
    /// Function can be called only by staking itself.
    function completePendingRoundChunk(uint32 roundId, uint8 chunkSize) public {
        require(msg.sender == address(this), 120);
        (bool exists, Round round) = _roundFetchPendingRound(roundId);
        if (exists) {
            tvm.accept();
            _setOrDeletePendingRound(_returnOrReinvest(round, chunkSize));
        }
    }


    /*
     * -------------- Public functions called by elector contract only --------------------------
     */

    // Called by Elector in process_new_stake function if our stake is accepted in elections.
    function receiveConfirmation(uint64 queryId, uint32 comment) public override onlyElector {
        require(comment == 0, 110);
        require(queryId >= 0, 110);
        // TODO: think how to use this confirmation
        // e.g. In case of unexpected failure we can notify user.
    }

    // Called by Elector in process_new_stake function if error occurred.
    function receiveReturnedStake(uint64 queryId, uint32 comment) public override onlyElector
        returns (uint64 _queryId, uint32 _comment)
    {
        Round round = _getPenultimateRound();
        round.completionStatus = ROUND_STAKE_REJECTED;

        // TODO: it is a bug here that status is not saved?
        // Can we add a test for this bug _before_ fixing it?

        _setPenultimateRound(_completeRound(_getPenultimateRound(), MAX_MSGS_PER_TR));
        // The return value is for logging, to catch outbound external message
        // and print queryId and comment.
        // TODO: in new version of sol2tvm compiler `return` don't emit ext msg if function is called by internal msg
        // delete `return` or use `emit`
        // https://github.com/tonlabs/sol2tvm/blob/dev/docs/API.md#return
        return (queryId, comment);
    }

    // Called by Elector contract as answer to recover_stake request.
    function acceptRecoveredStake(uint64 queryId) public override onlyElector {
        if (queryId == 0) {
            _acceptUnusedStake();
        } else if (queryId == 1) {
            _acceptRewardStake();
        } else {
            _acceptPendingRoundStake(uint32(queryId));
        }
    }

    /*
     * ----------- Owner functions ---------------------
     */

    /// @dev Allows to close pool or complete pending round.
    /// Closed pool restricts deposit stakes. Stakes in last round are sent to
    /// stakeholder's wallets immediately. Stakes in other rounds will be returned
    /// when rounds will be completed.
    function terminator(uint8 chunkSize) public onlyOwner {
        require(!m_poolClosed, 114);
        m_poolClosed = true;
        tvm.accept();
        if (_getRoundsCount() != 0) {
            Round lastRound = _getLastRound();
            lastRound.completionStatus = ROUND_POOL_CLOSED;
            _setLastRound(_completeRound(lastRound, chunkSize));
        }
        emit stakingPoolClosed();
    }

    /*
     * Fallback function.
     */

    // TODO forbid plain transfer and add function to receive funds
    // receive() { revert(...); }
    receive() external {}
    fallback() external {}
}

contract DePool is StakingContract {

    /// @dev Constructor with the elector address, the 1st node in node pool, the owner and elections parameters.
    constructor(
        address electorAddr,
        address poolOwnerAddr,
        uint32 electionId,
        address nodeWallet,
        uint32 beginBefore,
        uint32 endBefore,
        uint32 heldFor,
        uint32 electedFor,
        uint64 minStake,
        uint64 minRoundStake,
        uint64 maxRoundStake
    )
        StakingContract(
            electorAddr, poolOwnerAddr, electionId, nodeWallet,
            beginBefore, endBefore, heldFor, electedFor,
            minStake, minRoundStake, maxRoundStake ) public {
    }

    ////////////////////////////////////////////////////////////////////////////////////////////////////////////////////
    //// Public Getters

    /// @dev Get-method that returns reward value of staking pool owner.
    function getOwnerReward() public view returns (uint64 reward) {
        reward = m_owner.reward;
    }

    /* ---------- ROUNDS ---------- */

    /// @dev Allows to query information about all active staking rounds.
    function getRounds() public view returns (uint32 count, uint32 lastRound, RoundInfo[] infos) {
        infos = _getRoundsInfo();
        count = _getRoundsCount();
        lastRound = _getElectAt();
    }

    // Helper structure to return stakes in every round for one stakeholder.
    struct StakeInfo {
        uint32 roundId;
        uint64 stake;
        uint64 vesting;
    }

    /// @dev Allows to check stakeholder's information in all rounds.
    function getStakeholderInfo(address addr) public view
        returns (uint64 total, uint64 available, uint64 invested,
                 bool reinvest, uint64 reward, StakeInfo[] stakes)
                // TODO use mapping (uint32 => uint64) stakes, delete struct StakeInfo
    {
        require(_stakeholderExists(addr), 116);
        Stakeholder stakeholder = _getStakeholder(addr);
        reinvest = stakeholder.reinvest;
        total = stakeholder.totalStake;
        reward = stakeholder.grossReward;
        available = stakeholder.unusedStake;
        invested = total - available;

        // TODO: m_rounds should be accessed only from RoundsBase
        uint64 invested2 = 0; // This for debugging
        (uint64 index, Round round, bool ok) = m_rounds.min();
        while (ok) {
            if (round.step < STEP_COMPLETED) {
                (bool presents, StakeValue value) = round.stakes.fetch(addr);
                if (presents) {
                    stakes.push(StakeInfo(round.id, value.simple, value.vesting));
                    invested2 += value.simple + value.vesting;
                }
            } else {
                (bool presents, StakeValue value) = round.stakes.fetch(addr);
                if (presents) {
                    invested2 += value.simple + value.vesting;
                }
            }
            (index, round, ok) = m_rounds.next(index);
        }


        (index, round, ok) = m_pendingRounds.min();
        while (ok) {
            (bool presents, StakeValue value) = round.stakes.fetch(addr);
            if (presents) {
                invested2 += value.simple + value.vesting;
            }
            (index, round, ok) = m_pendingRounds.next(uint32(index));
        }
        //require(invested == invested2, 99);
    }

    /// @dev Allows to get minimal stakeholder's stake value
    function getMinStake() public view returns (uint64 minStake) {
        minStake = m_minStake;
    }

    function getStakingInfo() public view
        returns (uint64 minStake,
                 uint64 minRoundStake,
                 uint64 maxRoundStake,
                 uint64 minNodeStake,
                 uint32 stakingPeriod,
                 uint64 interest,
                 uint64 notifyFee,
                 uint64 addFee,
                 uint64 removeFee,
                 uint64 pauseFee,
                 uint64 continueFee,
                 uint64 setReinvestFee)
    {
        minStake = m_minStake;
        minRoundStake = m_minRoundStake;
        maxRoundStake = m_maxRoundStake;
        stakingPeriod = _getStakingPeriod();
        interest = m_lastRoundInterest;
        notifyFee = NOTIFY_FEE;
        addFee = ADD_STAKE_FEE;
        removeFee = REMOVE_STAKE_FEE;
        pauseFee = PAUSE_STAKE_FEE;
        continueFee = CONTINUE_STAKE_FEE;
        setReinvestFee = SET_REINVEST_FEE;
        minNodeStake = (m_minRoundStake * NODE_WALLET_MIN_STAKE) / 100;
    }

    // get-method for querying node controlled by staking pool
    function getValidator() public view returns (Node validator) {
        validator = m_node;
    }

    /// @dev Returns array of pending rounds.
    function getPendingRounds() public view returns (RoundInfo[] infos) {
        infos = _getPendingRoundsInfo();
    }
}
pragma solidity >=0.6.0;
pragma experimental ABIEncoderV2;

interface IStaking {
    //0xf374484c
    function receiveConfirmation(uint64 queryId, uint32 comment) external functionID(0xf374484c);
    //0xf96f7324
    function acceptRecoveredStake(uint64 queryId) external functionID(0xf96f7324);
    //0xFFFFFFFE
    function sendError(uint64 queryId, uint32 op) external;
}

contract TestElector {

    struct Validator {
        uint64 stake;
        uint256 key;
        uint64 reward;
        uint64 qid;
        uint32 factor;
        uint256 adnl;
        bytes signature;
    }

    mapping(uint256 => Validator) elections;

    uint32 electAt;
    uint32 constant ELECTIONS_BEGIN_BEFORE = 12;
    uint32 constant ELECTIONS_END_BEFORE = 6;
    uint32 constant ELECTED_FOR = 24;
    uint32 constant STAKE_HELD_FOR = 12;

    constructor(uint32 offset) public {
        electAt = uint32(now) + offset;
    }

    function getElectionId() public view returns (uint32) {
        return electAt;
    }

    //id = 0x4e73744b
    function process_new_stake(
        uint64 queryId,
        uint256 validatorKey,
        uint32 stakeAt,
        uint32 maxFactor,
        uint256 adnlAddr,
        bytes signature
    ) public functionID(0x4e73744b)
    {
        require(msg.sender != address(0), 101);
        uint32 nowtime = uint32(now);
        if (nowtime >= electAt) {
            electAt += ((nowtime - electAt) / ELECTED_FOR + 1) * ELECTED_FOR;
        }
        require(nowtime >= (electAt - ELECTIONS_BEGIN_BEFORE), 103);
        require(nowtime < (electAt - ELECTIONS_END_BEFORE), 103);
        require(electAt == stakeAt, 102);
        require(msg.value >= 100000000000, 104);

        (, uint256 addr) = msg.sender.unpack();
        elections[addr] = Validator(
            uint64(msg.value) - 1e9, validatorKey, 10000000000, queryId, maxFactor, adnlAddr, signature
        );
        IStaking(msg.sender).receiveConfirmation.value(1000000000)(queryId, 0);
    }

    //id = 0x47657424
    function recover_stake(uint64 queryId) public functionID(0x47657424) {
        (, uint256 addr) = msg.sender.unpack();
        (bool exists, Validator node) = elections.fetch(addr);
        require(exists, 107);
        uint32 time = uint32(now);
        if ((time > electAt) && time < (electAt + ELECTED_FOR + STAKE_HELD_FOR)) {
            IStaking(msg.sender).sendError.value(1000000000)(queryId, 0x47657424);
        } else {
            IStaking(msg.sender).acceptRecoveredStake.value(node.stake + node.reward)(queryId);
            delete elections[addr];
        }
    }

    receive() external {}
    fallback() external {}
}