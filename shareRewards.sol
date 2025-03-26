/*
 __     ___      _     _    _____ _             _                   
 \ \   / (_)    | |   | |  / ____| |           | |                  
  \ \_/ / _  ___| | __| | | (___ | |_ _ __ __ _| |_ ___  __ _ _   _ 
   \   / | |/ _ \ |/ _` |  \___ \| __| '__/ _` | __/ _ \/ _` | | | |
    | |  | |  __/ | (_| |  ____) | |_| | | (_| | ||  __/ (_| | |_| |
    |_|  |_|\___|_|\__,_| |_____/ \__|_|  \__,_|\__\___|\__, |\__, |
                                                         __/ | __/ |
                                                        |___/ |___/ 
*/

// SPDX-License-Identifier: MIT

pragma solidity ^0.8.0;

/**
 * @dev Contract module that helps prevent reentrant calls to a function.
 *
 * Inheriting from `ReentrancyGuard` will make the {nonReentrant} modifier
 * available, which can be applied to functions to make sure there are no nested
 * (reentrant) calls to them.
 *
 * Note that because there is a single `nonReentrant` guard, functions marked as
 * `nonReentrant` may not call one another. This can be worked around by making
 * those functions `private`, and then adding `external` `nonReentrant` entry
 * points to them.
 *
 * TIP: If you would like to learn more about reentrancy and alternative ways
 * to protect against it, check out our blog post
 * https://blog.openzeppelin.com/reentrancy-after-istanbul/[Reentrancy After Istanbul].
 */
abstract contract ReentrancyGuard {
    // Booleans are more expensive than uint256 or any type that takes up a full
    // word because each write operation emits an extra SLOAD to first read the
    // slot's contents, replace the bits taken up by the boolean, and then write
    // back. This is the compiler's defense against contract upgrades and
    // pointer aliasing, and it cannot be disabled.

    // The values being non-zero value makes deployment a bit more expensive,
    // but in exchange the refund on every call to nonReentrant will be lower in
    // amount. Since refunds are capped to a percentage of the total
    // transaction's gas, it is best to keep them low in cases like this one, to
    // increase the likelihood of the full refund coming into effect.
    uint256 private constant _NOT_ENTERED = 1;
    uint256 private constant _ENTERED = 2;

    uint256 private _status;

    constructor() {
        _status = _NOT_ENTERED;
    }

    /**
     * @dev Prevents a contract from calling itself, directly or indirectly.
     * Calling a `nonReentrant` function from another `nonReentrant`
     * function is not supported. It is possible to prevent this from happening
     * by making the `nonReentrant` function external, and making it call a
     * `private` function that does the actual work.
     */
    modifier nonReentrant() {
        _nonReentrantBefore();
        _;
        _nonReentrantAfter();
    }

    function _nonReentrantBefore() private {
        // On the first call to nonReentrant, _status will be _NOT_ENTERED
        require(_status != _ENTERED, "ReentrancyGuard: reentrant call");

        // Any calls to nonReentrant after this point will fail
        _status = _ENTERED;
    }

    function _nonReentrantAfter() private {
        // By storing the original value once again, a refund is triggered (see
        // https://eips.ethereum.org/EIPS/eip-2200)
        _status = _NOT_ENTERED;
    }

    /**
     * @dev Returns true if the reentrancy guard is currently set to "entered", which indicates there is a
     * `nonReentrant` function in the call stack.
     */
    function _reentrancyGuardEntered() internal view returns (bool) {
        return _status == _ENTERED;
    }
}


/**
 * @dev Interface of the ERC20 Permit extension allowing approvals to be made via signatures, as defined in
 * https://eips.ethereum.org/EIPS/eip-2612[EIP-2612].
 *
 * Adds the {permit} method, which can be used to change an account's ERC20 allowance (see {IERC20-allowance}) by
 * presenting a message signed by the account. By not relying on {IERC20-approve}, the token holder account doesn't
 * need to send a transaction, and thus is not required to hold Ether at all.
 *
 * ==== Security Considerations
 *
 * There are two important considerations concerning the use of `permit`. The first is that a valid permit signature
 * expresses an allowance, and it should not be assumed to convey additional meaning. In particular, it should not be
 * considered as an intention to spend the allowance in any specific way. The second is that because permits have
 * built-in replay protection and can be submitted by anyone, they can be frontrun. A protocol that uses permits should
 * take this into consideration and allow a `permit` call to fail. Combining these two aspects, a pattern that may be
 * generally recommended is:
 *
 * ```solidity
 * function doThingWithPermit(..., uint256 value, uint256 deadline, uint8 v, bytes32 r, bytes32 s) public {
 *     try token.permit(msg.sender, address(this), value, deadline, v, r, s) {} catch {}
 *     doThing(..., value);
 * }
 *
 * function doThing(..., uint256 value) public {
 *     token.safeTransferFrom(msg.sender, address(this), value);
 *     ...
 * }
 * ```
 *
 * Observe that: 1) `msg.sender` is used as the owner, leaving no ambiguity as to the signer intent, and 2) the use of
 * `try/catch` allows the permit to fail and makes the code tolerant to frontrunning. (See also
 * {SafeERC20-safeTransferFrom}).
 *
 * Additionally, note that smart contract wallets (such as Argent or Safe) are not able to produce permit signatures, so
 * contracts should have entry points that don't rely on permit.
 */
interface IERC20Permit {
    /**
     * @dev Sets `value` as the allowance of `spender` over ``owner``'s tokens,
     * given ``owner``'s signed approval.
     *
     * IMPORTANT: The same issues {IERC20-approve} has related to transaction
     * ordering also apply here.
     *
     * Emits an {Approval} event.
     *
     * Requirements:
     *
     * - `spender` cannot be the zero address.
     * - `deadline` must be a timestamp in the future.
     * - `v`, `r` and `s` must be a valid `secp256k1` signature from `owner`
     * over the EIP712-formatted function arguments.
     * - the signature must use ``owner``'s current nonce (see {nonces}).
     *
     * For more information on the signature format, see the
     * https://eips.ethereum.org/EIPS/eip-2612#specification[relevant EIP
     * section].
     *
     * CAUTION: See Security Considerations above.
     */
    function permit(
        address owner,
        address spender,
        uint256 value,
        uint256 deadline,
        uint8 v,
        bytes32 r,
        bytes32 s
    ) external;

    /**
     * @dev Returns the current nonce for `owner`. This value must be
     * included whenever a signature is generated for {permit}.
     *
     * Every successful call to {permit} increases ``owner``'s nonce by one. This
     * prevents a signature from being used multiple times.
     */
    function nonces(address owner) external view returns (uint256);

    /**
     * @dev Returns the domain separator used in the encoding of the signature for {permit}, as defined by {EIP712}.
     */
    // solhint-disable-next-line func-name-mixedcase
    function DOMAIN_SEPARATOR() external view returns (bytes32);
}


/**
 * @dev Interface of the ERC20 standard as defined in the EIP.
 */
interface IERC20 {
    /**
     * @dev Emitted when `value` tokens are moved from one account (`from`) to
     * another (`to`).
     *
     * Note that `value` may be zero.
     */
    event Transfer(address indexed from, address indexed to, uint256 value);

    /**
     * @dev Emitted when the allowance of a `spender` for an `owner` is set by
     * a call to {approve}. `value` is the new allowance.
     */
    event Approval(address indexed owner, address indexed spender, uint256 value);

    /**
     * @dev Returns the amount of tokens in existence.
     */
    function totalSupply() external view returns (uint256);

    /**
     * @dev Returns the amount of tokens owned by `account`.
     */
    function balanceOf(address account) external view returns (uint256);

    /**
     * @dev Moves `amount` tokens from the caller's account to `to`.
     *
     * Returns a boolean value indicating whether the operation succeeded.
     *
     * Emits a {Transfer} event.
     */
    function transfer(address to, uint256 amount) external returns (bool);

    /**
     * @dev Returns the remaining number of tokens that `spender` will be
     * allowed to spend on behalf of `owner` through {transferFrom}. This is
     * zero by default.
     *
     * This value changes when {approve} or {transferFrom} are called.
     */
    function allowance(address owner, address spender) external view returns (uint256);

    /**
     * @dev Sets `amount` as the allowance of `spender` over the caller's tokens.
     *
     * Returns a boolean value indicating whether the operation succeeded.
     *
     * IMPORTANT: Beware that changing an allowance with this method brings the risk
     * that someone may use both the old and the new allowance by unfortunate
     * transaction ordering. One possible solution to mitigate this race
     * condition is to first reduce the spender's allowance to 0 and set the
     * desired value afterwards:
     * https://github.com/ethereum/EIPs/issues/20#issuecomment-263524729
     *
     * Emits an {Approval} event.
     */
    function approve(address spender, uint256 amount) external returns (bool);

    /**
     * @dev Moves `amount` tokens from `from` to `to` using the
     * allowance mechanism. `amount` is then deducted from the caller's
     * allowance.
     *
     * Returns a boolean value indicating whether the operation succeeded.
     *
     * Emits a {Transfer} event.
     */
    function transferFrom(address from, address to, uint256 amount) external returns (bool);
}

/**
 * @dev Interface for the optional metadata functions from the ERC20 standard.
 *
 * _Available since v4.1._
 */
interface IERC20Metadata is IERC20 {
    /**
     * @dev Returns the name of the token.
     */
    function name() external view returns (string memory);

    /**
     * @dev Returns the symbol of the token.
     */
    function symbol() external view returns (string memory);

    /**
     * @dev Returns the decimals places of the token.
     */
    function decimals() external view returns (uint8);
}


/**
 * @title SafeERC20
 * @dev Wrappers around ERC20 operations that throw on failure (when the token
 * contract returns false). Tokens that return no value (and instead revert or
 * throw on failure) are also supported, non-reverting calls are assumed to be
 * successful.
 * To use this library you can add a `using SafeERC20 for IERC20;` statement to your contract,
 * which allows you to call the safe operations as `token.safeTransfer(...)`, etc.
 */
library SafeERC20 {
    using Address for address;

    /**
     * @dev Transfer `value` amount of `token` from the calling contract to `to`. If `token` returns no value,
     * non-reverting calls are assumed to be successful.
     */
    function safeTransfer(IERC20 token, address to, uint256 value) internal {
        _callOptionalReturn(token, abi.encodeWithSelector(token.transfer.selector, to, value));
    }

    /**
     * @dev Transfer `value` amount of `token` from `from` to `to`, spending the approval given by `from` to the
     * calling contract. If `token` returns no value, non-reverting calls are assumed to be successful.
     */
    function safeTransferFrom(IERC20 token, address from, address to, uint256 value) internal {
        _callOptionalReturn(token, abi.encodeWithSelector(token.transferFrom.selector, from, to, value));
    }

    /**
     * @dev Deprecated. This function has issues similar to the ones found in
     * {IERC20-approve}, and its usage is discouraged.
     *
     * Whenever possible, use {safeIncreaseAllowance} and
     * {safeDecreaseAllowance} instead.
     */
    function safeApprove(IERC20 token, address spender, uint256 value) internal {
        // safeApprove should only be called when setting an initial allowance,
        // or when resetting it to zero. To increase and decrease it, use
        // 'safeIncreaseAllowance' and 'safeDecreaseAllowance'
        require(
            (value == 0) || (token.allowance(address(this), spender) == 0),
            "SafeERC20: approve from non-zero to non-zero allowance"
        );
        _callOptionalReturn(token, abi.encodeWithSelector(token.approve.selector, spender, value));
    }

    /**
     * @dev Increase the calling contract's allowance toward `spender` by `value`. If `token` returns no value,
     * non-reverting calls are assumed to be successful.
     */
    function safeIncreaseAllowance(IERC20 token, address spender, uint256 value) internal {
        uint256 oldAllowance = token.allowance(address(this), spender);
        _callOptionalReturn(token, abi.encodeWithSelector(token.approve.selector, spender, oldAllowance + value));
    }

    /**
     * @dev Decrease the calling contract's allowance toward `spender` by `value`. If `token` returns no value,
     * non-reverting calls are assumed to be successful.
     */
    function safeDecreaseAllowance(IERC20 token, address spender, uint256 value) internal {
        unchecked {
            uint256 oldAllowance = token.allowance(address(this), spender);
            require(oldAllowance >= value, "SafeERC20: decreased allowance below zero");
            _callOptionalReturn(token, abi.encodeWithSelector(token.approve.selector, spender, oldAllowance - value));
        }
    }

    /**
     * @dev Set the calling contract's allowance toward `spender` to `value`. If `token` returns no value,
     * non-reverting calls are assumed to be successful. Meant to be used with tokens that require the approval
     * to be set to zero before setting it to a non-zero value, such as USDT.
     */
    function forceApprove(IERC20 token, address spender, uint256 value) internal {
        bytes memory approvalCall = abi.encodeWithSelector(token.approve.selector, spender, value);

        if (!_callOptionalReturnBool(token, approvalCall)) {
            _callOptionalReturn(token, abi.encodeWithSelector(token.approve.selector, spender, 0));
            _callOptionalReturn(token, approvalCall);
        }
    }

    /**
     * @dev Use a ERC-2612 signature to set the `owner` approval toward `spender` on `token`.
     * Revert on invalid signature.
     */
    function safePermit(
        IERC20Permit token,
        address owner,
        address spender,
        uint256 value,
        uint256 deadline,
        uint8 v,
        bytes32 r,
        bytes32 s
    ) internal {
        uint256 nonceBefore = token.nonces(owner);
        token.permit(owner, spender, value, deadline, v, r, s);
        uint256 nonceAfter = token.nonces(owner);
        require(nonceAfter == nonceBefore + 1, "SafeERC20: permit did not succeed");
    }

    /**
     * @dev Imitates a Solidity high-level call (i.e. a regular function call to a contract), relaxing the requirement
     * on the return value: the return value is optional (but if data is returned, it must not be false).
     * @param token The token targeted by the call.
     * @param data The call data (encoded using abi.encode or one of its variants).
     */
    function _callOptionalReturn(IERC20 token, bytes memory data) private {
        // We need to perform a low level call here, to bypass Solidity's return data size checking mechanism, since
        // we're implementing it ourselves. We use {Address-functionCall} to perform this call, which verifies that
        // the target address contains contract code and also asserts for success in the low-level call.

        bytes memory returndata = address(token).functionCall(data, "SafeERC20: low-level call failed");
        require(returndata.length == 0 || abi.decode(returndata, (bool)), "SafeERC20: ERC20 operation did not succeed");
    }

    /**
     * @dev Imitates a Solidity high-level call (i.e. a regular function call to a contract), relaxing the requirement
     * on the return value: the return value is optional (but if data is returned, it must not be false).
     * @param token The token targeted by the call.
     * @param data The call data (encoded using abi.encode or one of its variants).
     *
     * This is a variant of {_callOptionalReturn} that silents catches all reverts and returns a bool instead.
     */
    function _callOptionalReturnBool(IERC20 token, bytes memory data) private returns (bool) {
        // We need to perform a low level call here, to bypass Solidity's return data size checking mechanism, since
        // we're implementing it ourselves. We cannot use {Address-functionCall} here since this should return false
        // and not revert is the subcall reverts.

        (bool success, bytes memory returndata) = address(token).call(data);
        return
            success && (returndata.length == 0 || abi.decode(returndata, (bool))) && Address.isContract(address(token));
    }
}


/**
 * @dev Collection of functions related to the address type
 */
library Address {
    /**
     * @dev Returns true if `account` is a contract.
     *
     * [IMPORTANT]
     * ====
     * It is unsafe to assume that an address for which this function returns
     * false is an externally-owned account (EOA) and not a contract.
     *
     * Among others, `isContract` will return false for the following
     * types of addresses:
     *
     *  - an externally-owned account
     *  - a contract in construction
     *  - an address where a contract will be created
     *  - an address where a contract lived, but was destroyed
     *
     * Furthermore, `isContract` will also return true if the target contract within
     * the same transaction is already scheduled for destruction by `SELFDESTRUCT`,
     * which only has an effect at the end of a transaction.
     * ====
     *
     * [IMPORTANT]
     * ====
     * You shouldn't rely on `isContract` to protect against flash loan attacks!
     *
     * Preventing calls from contracts is highly discouraged. It breaks composability, breaks support for smart wallets
     * like Gnosis Safe, and does not provide security since it can be circumvented by calling from a contract
     * constructor.
     * ====
     */
    function isContract(address account) internal view returns (bool) {
        // This method relies on extcodesize/address.code.length, which returns 0
        // for contracts in construction, since the code is only stored at the end
        // of the constructor execution.

        return account.code.length > 0;
    }

    /**
     * @dev Replacement for Solidity's `transfer`: sends `amount` wei to
     * `recipient`, forwarding all available gas and reverting on errors.
     *
     * https://eips.ethereum.org/EIPS/eip-1884[EIP1884] increases the gas cost
     * of certain opcodes, possibly making contracts go over the 2300 gas limit
     * imposed by `transfer`, making them unable to receive funds via
     * `transfer`. {sendValue} removes this limitation.
     *
     * https://consensys.net/diligence/blog/2019/09/stop-using-soliditys-transfer-now/[Learn more].
     *
     * IMPORTANT: because control is transferred to `recipient`, care must be
     * taken to not create reentrancy vulnerabilities. Consider using
     * {ReentrancyGuard} or the
     * https://solidity.readthedocs.io/en/v0.8.0/security-considerations.html#use-the-checks-effects-interactions-pattern[checks-effects-interactions pattern].
     */
    function sendValue(address payable recipient, uint256 amount) internal {
        require(address(this).balance >= amount, "Address: insufficient balance");

        (bool success, ) = recipient.call{value: amount}("");
        require(success, "Address: unable to send value, recipient may have reverted");
    }

    /**
     * @dev Performs a Solidity function call using a low level `call`. A
     * plain `call` is an unsafe replacement for a function call: use this
     * function instead.
     *
     * If `target` reverts with a revert reason, it is bubbled up by this
     * function (like regular Solidity function calls).
     *
     * Returns the raw returned data. To convert to the expected return value,
     * use https://solidity.readthedocs.io/en/latest/units-and-global-variables.html?highlight=abi.decode#abi-encoding-and-decoding-functions[`abi.decode`].
     *
     * Requirements:
     *
     * - `target` must be a contract.
     * - calling `target` with `data` must not revert.
     *
     * _Available since v3.1._
     */
    function functionCall(address target, bytes memory data) internal returns (bytes memory) {
        return functionCallWithValue(target, data, 0, "Address: low-level call failed");
    }

    /**
     * @dev Same as {xref-Address-functionCall-address-bytes-}[`functionCall`], but with
     * `errorMessage` as a fallback revert reason when `target` reverts.
     *
     * _Available since v3.1._
     */
    function functionCall(
        address target,
        bytes memory data,
        string memory errorMessage
    ) internal returns (bytes memory) {
        return functionCallWithValue(target, data, 0, errorMessage);
    }

    /**
     * @dev Same as {xref-Address-functionCall-address-bytes-}[`functionCall`],
     * but also transferring `value` wei to `target`.
     *
     * Requirements:
     *
     * - the calling contract must have an ETH balance of at least `value`.
     * - the called Solidity function must be `payable`.
     *
     * _Available since v3.1._
     */
    function functionCallWithValue(address target, bytes memory data, uint256 value) internal returns (bytes memory) {
        return functionCallWithValue(target, data, value, "Address: low-level call with value failed");
    }

    /**
     * @dev Same as {xref-Address-functionCallWithValue-address-bytes-uint256-}[`functionCallWithValue`], but
     * with `errorMessage` as a fallback revert reason when `target` reverts.
     *
     * _Available since v3.1._
     */
    function functionCallWithValue(
        address target,
        bytes memory data,
        uint256 value,
        string memory errorMessage
    ) internal returns (bytes memory) {
        require(address(this).balance >= value, "Address: insufficient balance for call");
        (bool success, bytes memory returndata) = target.call{value: value}(data);
        return verifyCallResultFromTarget(target, success, returndata, errorMessage);
    }

    /**
     * @dev Same as {xref-Address-functionCall-address-bytes-}[`functionCall`],
     * but performing a static call.
     *
     * _Available since v3.3._
     */
    function functionStaticCall(address target, bytes memory data) internal view returns (bytes memory) {
        return functionStaticCall(target, data, "Address: low-level static call failed");
    }

    /**
     * @dev Same as {xref-Address-functionCall-address-bytes-string-}[`functionCall`],
     * but performing a static call.
     *
     * _Available since v3.3._
     */
    function functionStaticCall(
        address target,
        bytes memory data,
        string memory errorMessage
    ) internal view returns (bytes memory) {
        (bool success, bytes memory returndata) = target.staticcall(data);
        return verifyCallResultFromTarget(target, success, returndata, errorMessage);
    }

    /**
     * @dev Same as {xref-Address-functionCall-address-bytes-}[`functionCall`],
     * but performing a delegate call.
     *
     * _Available since v3.4._
     */
    function functionDelegateCall(address target, bytes memory data) internal returns (bytes memory) {
        return functionDelegateCall(target, data, "Address: low-level delegate call failed");
    }

    /**
     * @dev Same as {xref-Address-functionCall-address-bytes-string-}[`functionCall`],
     * but performing a delegate call.
     *
     * _Available since v3.4._
     */
    function functionDelegateCall(
        address target,
        bytes memory data,
        string memory errorMessage
    ) internal returns (bytes memory) {
        (bool success, bytes memory returndata) = target.delegatecall(data);
        return verifyCallResultFromTarget(target, success, returndata, errorMessage);
    }

    /**
     * @dev Tool to verify that a low level call to smart-contract was successful, and revert (either by bubbling
     * the revert reason or using the provided one) in case of unsuccessful call or if target was not a contract.
     *
     * _Available since v4.8._
     */
    function verifyCallResultFromTarget(
        address target,
        bool success,
        bytes memory returndata,
        string memory errorMessage
    ) internal view returns (bytes memory) {
        if (success) {
            if (returndata.length == 0) {
                // only check isContract if the call was successful and the return data is empty
                // otherwise we already know that it was a contract
                require(isContract(target), "Address: call to non-contract");
            }
            return returndata;
        } else {
            _revert(returndata, errorMessage);
        }
    }

    /**
     * @dev Tool to verify that a low level call was successful, and revert if it wasn't, either by bubbling the
     * revert reason or using the provided one.
     *
     * _Available since v4.3._
     */
    function verifyCallResult(
        bool success,
        bytes memory returndata,
        string memory errorMessage
    ) internal pure returns (bytes memory) {
        if (success) {
            return returndata;
        } else {
            _revert(returndata, errorMessage);
        }
    }

    function _revert(bytes memory returndata, string memory errorMessage) private pure {
        // Look for revert reason and bubble it up if present
        if (returndata.length > 0) {
            // The easiest way to bubble the revert reason is using memory via assembly
            /// @solidity memory-safe-assembly
            assembly {
                let returndata_size := mload(returndata)
                revert(add(32, returndata), returndata_size)
            }
        } else {
            revert(errorMessage);
        }
    }
}


// CAUTION
// This version of SafeMath should only be used with Solidity 0.8 or later,
// because it relies on the compiler's built in overflow checks.

/**
 * @dev Wrappers over Solidity's arithmetic operations.
 *
 * NOTE: `SafeMath` is generally not needed starting with Solidity 0.8, since the compiler
 * now has built in overflow checking.
 */
library SafeMath {
    /**
     * @dev Returns the addition of two unsigned integers, with an overflow flag.
     *
     * _Available since v3.4._
     */
    function tryAdd(uint256 a, uint256 b) internal pure returns (bool, uint256) {
        unchecked {
            uint256 c = a + b;
            if (c < a) return (false, 0);
            return (true, c);
        }
    }

    /**
     * @dev Returns the subtraction of two unsigned integers, with an overflow flag.
     *
     * _Available since v3.4._
     */
    function trySub(uint256 a, uint256 b) internal pure returns (bool, uint256) {
        unchecked {
            if (b > a) return (false, 0);
            return (true, a - b);
        }
    }

    /**
     * @dev Returns the multiplication of two unsigned integers, with an overflow flag.
     *
     * _Available since v3.4._
     */
    function tryMul(uint256 a, uint256 b) internal pure returns (bool, uint256) {
        unchecked {
            // Gas optimization: this is cheaper than requiring 'a' not being zero, but the
            // benefit is lost if 'b' is also tested.
            // See: https://github.com/OpenZeppelin/openzeppelin-contracts/pull/522
            if (a == 0) return (true, 0);
            uint256 c = a * b;
            if (c / a != b) return (false, 0);
            return (true, c);
        }
    }

    /**
     * @dev Returns the division of two unsigned integers, with a division by zero flag.
     *
     * _Available since v3.4._
     */
    function tryDiv(uint256 a, uint256 b) internal pure returns (bool, uint256) {
        unchecked {
            if (b == 0) return (false, 0);
            return (true, a / b);
        }
    }

    /**
     * @dev Returns the remainder of dividing two unsigned integers, with a division by zero flag.
     *
     * _Available since v3.4._
     */
    function tryMod(uint256 a, uint256 b) internal pure returns (bool, uint256) {
        unchecked {
            if (b == 0) return (false, 0);
            return (true, a % b);
        }
    }

    /**
     * @dev Returns the addition of two unsigned integers, reverting on
     * overflow.
     *
     * Counterpart to Solidity's `+` operator.
     *
     * Requirements:
     *
     * - Addition cannot overflow.
     */
    function add(uint256 a, uint256 b) internal pure returns (uint256) {
        return a + b;
    }

    /**
     * @dev Returns the subtraction of two unsigned integers, reverting on
     * overflow (when the result is negative).
     *
     * Counterpart to Solidity's `-` operator.
     *
     * Requirements:
     *
     * - Subtraction cannot overflow.
     */
    function sub(uint256 a, uint256 b) internal pure returns (uint256) {
        return a - b;
    }

    /**
     * @dev Returns the multiplication of two unsigned integers, reverting on
     * overflow.
     *
     * Counterpart to Solidity's `*` operator.
     *
     * Requirements:
     *
     * - Multiplication cannot overflow.
     */
    function mul(uint256 a, uint256 b) internal pure returns (uint256) {
        return a * b;
    }

    /**
     * @dev Returns the integer division of two unsigned integers, reverting on
     * division by zero. The result is rounded towards zero.
     *
     * Counterpart to Solidity's `/` operator.
     *
     * Requirements:
     *
     * - The divisor cannot be zero.
     */
    function div(uint256 a, uint256 b) internal pure returns (uint256) {
        return a / b;
    }

    /**
     * @dev Returns the remainder of dividing two unsigned integers. (unsigned integer modulo),
     * reverting when dividing by zero.
     *
     * Counterpart to Solidity's `%` operator. This function uses a `revert`
     * opcode (which leaves remaining gas untouched) while Solidity uses an
     * invalid opcode to revert (consuming all remaining gas).
     *
     * Requirements:
     *
     * - The divisor cannot be zero.
     */
    function mod(uint256 a, uint256 b) internal pure returns (uint256) {
        return a % b;
    }

    /**
     * @dev Returns the subtraction of two unsigned integers, reverting with custom message on
     * overflow (when the result is negative).
     *
     * CAUTION: This function is deprecated because it requires allocating memory for the error
     * message unnecessarily. For custom revert reasons use {trySub}.
     *
     * Counterpart to Solidity's `-` operator.
     *
     * Requirements:
     *
     * - Subtraction cannot overflow.
     */
    function sub(uint256 a, uint256 b, string memory errorMessage) internal pure returns (uint256) {
        unchecked {
            require(b <= a, errorMessage);
            return a - b;
        }
    }

    /**
     * @dev Returns the integer division of two unsigned integers, reverting with custom message on
     * division by zero. The result is rounded towards zero.
     *
     * Counterpart to Solidity's `/` operator. Note: this function uses a
     * `revert` opcode (which leaves remaining gas untouched) while Solidity
     * uses an invalid opcode to revert (consuming all remaining gas).
     *
     * Requirements:
     *
     * - The divisor cannot be zero.
     */
    function div(uint256 a, uint256 b, string memory errorMessage) internal pure returns (uint256) {
        unchecked {
            require(b > 0, errorMessage);
            return a / b;
        }
    }

    /**
     * @dev Returns the remainder of dividing two unsigned integers. (unsigned integer modulo),
     * reverting with custom message when dividing by zero.
     *
     * CAUTION: This function is deprecated because it requires allocating memory for the error
     * message unnecessarily. For custom revert reasons use {tryMod}.
     *
     * Counterpart to Solidity's `%` operator. This function uses a `revert`
     * opcode (which leaves remaining gas untouched) while Solidity uses an
     * invalid opcode to revert (consuming all remaining gas).
     *
     * Requirements:
     *
     * - The divisor cannot be zero.
     */
    function mod(uint256 a, uint256 b, string memory errorMessage) internal pure returns (uint256) {
        unchecked {
            require(b > 0, errorMessage);
            return a % b;
        }
    }
}


/**
 * @dev Interface of the ERC-4626 "Tokenized Vault Standard", as defined in
 * https://eips.ethereum.org/EIPS/eip-4626[ERC-4626].
 */
interface IERC4626 is IERC20, IERC20Metadata {
    event Deposit(address indexed sender, address indexed owner, uint256 assets, uint256 shares);

    event Withdraw(
        address indexed sender,
        address indexed receiver,
        address indexed owner,
        uint256 assets,
        uint256 shares
    );

    /**
     * @dev Returns the address of the underlying token used for the Vault for accounting, depositing, and withdrawing.
     *
     * - MUST be an ERC-20 token contract.
     * - MUST NOT revert.
     */
    function asset() external view returns (address assetTokenAddress);

    /**
     * @dev Returns the total amount of the underlying asset that is “managed” by Vault.
     *
     * - SHOULD include any compounding that occurs from yield.
     * - MUST be inclusive of any fees that are charged against assets in the Vault.
     * - MUST NOT revert.
     */
    function totalAssets() external view returns (uint256 totalManagedAssets);

    /**
     * @dev Returns the amount of shares that the Vault would exchange for the amount of assets provided, in an ideal
     * scenario where all the conditions are met.
     *
     * - MUST NOT be inclusive of any fees that are charged against assets in the Vault.
     * - MUST NOT show any variations depending on the caller.
     * - MUST NOT reflect slippage or other on-chain conditions, when performing the actual exchange.
     * - MUST NOT revert.
     *
     * NOTE: This calculation MAY NOT reflect the “per-user” price-per-share, and instead should reflect the
     * “average-user’s” price-per-share, meaning what the average user should expect to see when exchanging to and
     * from.
     */
    function convertToShares(uint256 assets) external view returns (uint256 shares);

    /**
     * @dev Returns the amount of assets that the Vault would exchange for the amount of shares provided, in an ideal
     * scenario where all the conditions are met.
     *
     * - MUST NOT be inclusive of any fees that are charged against assets in the Vault.
     * - MUST NOT show any variations depending on the caller.
     * - MUST NOT reflect slippage or other on-chain conditions, when performing the actual exchange.
     * - MUST NOT revert.
     *
     * NOTE: This calculation MAY NOT reflect the “per-user” price-per-share, and instead should reflect the
     * “average-user’s” price-per-share, meaning what the average user should expect to see when exchanging to and
     * from.
     */
    function convertToAssets(uint256 shares) external view returns (uint256 assets);

    /**
     * @dev Returns the maximum amount of the underlying asset that can be deposited into the Vault for the receiver,
     * through a deposit call.
     *
     * - MUST return a limited value if receiver is subject to some deposit limit.
     * - MUST return 2 ** 256 - 1 if there is no limit on the maximum amount of assets that may be deposited.
     * - MUST NOT revert.
     */
    function maxDeposit(address receiver) external view returns (uint256 maxAssets);

    /**
     * @dev Allows an on-chain or off-chain user to simulate the effects of their deposit at the current block, given
     * current on-chain conditions.
     *
     * - MUST return as close to and no more than the exact amount of Vault shares that would be minted in a deposit
     *   call in the same transaction. I.e. deposit should return the same or more shares as previewDeposit if called
     *   in the same transaction.
     * - MUST NOT account for deposit limits like those returned from maxDeposit and should always act as though the
     *   deposit would be accepted, regardless if the user has enough tokens approved, etc.
     * - MUST be inclusive of deposit fees. Integrators should be aware of the existence of deposit fees.
     * - MUST NOT revert.
     *
     * NOTE: any unfavorable discrepancy between convertToShares and previewDeposit SHOULD be considered slippage in
     * share price or some other type of condition, meaning the depositor will lose assets by depositing.
     */
    function previewDeposit(uint256 assets) external view returns (uint256 shares);

    /**
     * @dev Mints shares Vault shares to receiver by depositing exactly amount of underlying tokens.
     *
     * - MUST emit the Deposit event.
     * - MAY support an additional flow in which the underlying tokens are owned by the Vault contract before the
     *   deposit execution, and are accounted for during deposit.
     * - MUST revert if all of assets cannot be deposited (due to deposit limit being reached, slippage, the user not
     *   approving enough underlying tokens to the Vault contract, etc).
     *
     * NOTE: most implementations will require pre-approval of the Vault with the Vault’s underlying asset token.
     */
    function deposit(uint256 assets, address receiver) external returns (uint256 shares);

    /**
     * @dev Returns the maximum amount of the Vault shares that can be minted for the receiver, through a mint call.
     * - MUST return a limited value if receiver is subject to some mint limit.
     * - MUST return 2 ** 256 - 1 if there is no limit on the maximum amount of shares that may be minted.
     * - MUST NOT revert.
     */
    function maxMint(address receiver) external view returns (uint256 maxShares);

    /**
     * @dev Allows an on-chain or off-chain user to simulate the effects of their mint at the current block, given
     * current on-chain conditions.
     *
     * - MUST return as close to and no fewer than the exact amount of assets that would be deposited in a mint call
     *   in the same transaction. I.e. mint should return the same or fewer assets as previewMint if called in the
     *   same transaction.
     * - MUST NOT account for mint limits like those returned from maxMint and should always act as though the mint
     *   would be accepted, regardless if the user has enough tokens approved, etc.
     * - MUST be inclusive of deposit fees. Integrators should be aware of the existence of deposit fees.
     * - MUST NOT revert.
     *
     * NOTE: any unfavorable discrepancy between convertToAssets and previewMint SHOULD be considered slippage in
     * share price or some other type of condition, meaning the depositor will lose assets by minting.
     */
    function previewMint(uint256 shares) external view returns (uint256 assets);

    /**
     * @dev Mints exactly shares Vault shares to receiver by depositing amount of underlying tokens.
     *
     * - MUST emit the Deposit event.
     * - MAY support an additional flow in which the underlying tokens are owned by the Vault contract before the mint
     *   execution, and are accounted for during mint.
     * - MUST revert if all of shares cannot be minted (due to deposit limit being reached, slippage, the user not
     *   approving enough underlying tokens to the Vault contract, etc).
     *
     * NOTE: most implementations will require pre-approval of the Vault with the Vault’s underlying asset token.
     */
    function mint(uint256 shares, address receiver) external returns (uint256 assets);

    /**
     * @dev Returns the maximum amount of the underlying asset that can be withdrawn from the owner balance in the
     * Vault, through a withdraw call.
     *
     * - MUST return a limited value if owner is subject to some withdrawal limit or timelock.
     * - MUST NOT revert.
     */
    function maxWithdraw(address owner) external view returns (uint256 maxAssets);

    /**
     * @dev Allows an on-chain or off-chain user to simulate the effects of their withdrawal at the current block,
     * given current on-chain conditions.
     *
     * - MUST return as close to and no fewer than the exact amount of Vault shares that would be burned in a withdraw
     *   call in the same transaction. I.e. withdraw should return the same or fewer shares as previewWithdraw if
     *   called
     *   in the same transaction.
     * - MUST NOT account for withdrawal limits like those returned from maxWithdraw and should always act as though
     *   the withdrawal would be accepted, regardless if the user has enough shares, etc.
     * - MUST be inclusive of withdrawal fees. Integrators should be aware of the existence of withdrawal fees.
     * - MUST NOT revert.
     *
     * NOTE: any unfavorable discrepancy between convertToShares and previewWithdraw SHOULD be considered slippage in
     * share price or some other type of condition, meaning the depositor will lose assets by depositing.
     */
    function previewWithdraw(uint256 assets) external view returns (uint256 shares);

    /**
     * @dev Burns shares from owner and sends exactly assets of underlying tokens to receiver.
     *
     * - MUST emit the Withdraw event.
     * - MAY support an additional flow in which the underlying tokens are owned by the Vault contract before the
     *   withdraw execution, and are accounted for during withdraw.
     * - MUST revert if all of assets cannot be withdrawn (due to withdrawal limit being reached, slippage, the owner
     *   not having enough shares, etc).
     *
     * Note that some implementations will require pre-requesting to the Vault before a withdrawal may be performed.
     * Those methods should be performed separately.
     */
    function withdraw(uint256 assets, address receiver, address owner) external returns (uint256 shares);

    /**
     * @dev Returns the maximum amount of Vault shares that can be redeemed from the owner balance in the Vault,
     * through a redeem call.
     *
     * - MUST return a limited value if owner is subject to some withdrawal limit or timelock.
     * - MUST return balanceOf(owner) if owner is not subject to any withdrawal limit or timelock.
     * - MUST NOT revert.
     */
    function maxRedeem(address owner) external view returns (uint256 maxShares);

    /**
     * @dev Allows an on-chain or off-chain user to simulate the effects of their redeemption at the current block,
     * given current on-chain conditions.
     *
     * - MUST return as close to and no more than the exact amount of assets that would be withdrawn in a redeem call
     *   in the same transaction. I.e. redeem should return the same or more assets as previewRedeem if called in the
     *   same transaction.
     * - MUST NOT account for redemption limits like those returned from maxRedeem and should always act as though the
     *   redemption would be accepted, regardless if the user has enough shares, etc.
     * - MUST be inclusive of withdrawal fees. Integrators should be aware of the existence of withdrawal fees.
     * - MUST NOT revert.
     *
     * NOTE: any unfavorable discrepancy between convertToAssets and previewRedeem SHOULD be considered slippage in
     * share price or some other type of condition, meaning the depositor will lose assets by redeeming.
     */
    function previewRedeem(uint256 shares) external view returns (uint256 assets);

    /**
     * @dev Burns exactly shares from owner and sends assets of underlying tokens to receiver.
     *
     * - MUST emit the Withdraw event.
     * - MAY support an additional flow in which the underlying tokens are owned by the Vault contract before the
     *   redeem execution, and are accounted for during redeem.
     * - MUST revert if all of shares cannot be redeemed (due to withdrawal limit being reached, slippage, the owner
     *   not having enough shares, etc).
     *
     * NOTE: some implementations will require pre-requesting to the Vault before a withdrawal may be performed.
     * Those methods should be performed separately.
     */
    function redeem(uint256 shares, address receiver, address owner) external returns (uint256 assets);
}

interface IBasisAsset {
    function mint(address recipient, uint256 amount) external returns (bool);

    function burn(uint256 amount) external;

    function burnFrom(address from, uint256 amount) external;

    function isOperator() external returns (bool);

    function operator() external view returns (address);

    function transferOperator(address newOperator_) external;
}


interface IOracle {
    function update() external;

    function consult(address _token, uint256 _amountIn) external view returns (uint256 amountOut);

    function twap(address _token, uint256 _amountIn) external view returns (uint256 _amountOut);
}


contract ShareRewardPool is ReentrancyGuard {
    using SafeMath for uint256;
    using SafeERC20 for IERC20;

    enum GaugeDex {
        NONE,
        SHADOW,
        SWAPX
    }

    // governance
    address public operator;

    // Info of each user.
    struct UserInfo {
        uint256 amount; // How many LP tokens the user has provided.
        uint256 rewardDebt; // Reward debt. See explanation below.
    }

    struct GaugeInfo {
        bool isGauge;   // If this is a gauge
        address gauge;  // The gauge
        GaugeDex gaugeDex; // Dex of the gauge
    }

    // Info of each pool.
    struct PoolInfo {
        IERC20 token; // Address of LP token contract.
        uint256 depFee; // deposit fee that is applied to created pool.
        uint256 allocPoint; // How many allocation points assigned to this pool. SHAREs to distribute per block.
        uint256 lastRewardTime; // Last time that SHAREs distribution occurs.
        uint256 accSharePerShare; // Accumulated SHAREs per share, times 1e18. See below.
        bool isStarted; // if lastRewardTime has passed
        GaugeInfo gaugeInfo; // Gauge info (does this pool have a gauge and where is it)
        uint256 poolSharePerSec; // rewards per second for pool (acts as allocPoint)
    }

    IERC20 public share;
    IOracle public shareOracle;
    bool public claimGaugeRewardsOnUpdatePool = true;
    bool public pegStabilityModuleFeeEnabled = true;
    bool public mustConvertXShadow = true;
    uint256 public pegStabilityModuleFee = 150; // 15%
    uint256 public minClaimThreshold = 1e12; // 0.000001 SHARE

    IShadowVoter public shadowVoter;
    ISwapxVoter public swapxVoter;
    address public constant XSHADOW_TOKEN = 0x5050bc082FF4A74Fb6B0B04385dEfdDB114b2424;
    address public constant X33_TOKEN = 0x3333111A391cC08fa51353E9195526A70b333333;
    address public constant X33_WRAPPER = 0x9710E10A8f6FbA8C391606fee18614885684548d;
    address public constant SWAPX_TOKEN = 0xA04BC7140c26fc9BB1F36B1A604C7A5a88fb0E70;

    address public bribesSafe;
    address public msigWallet;

    // Info of each pool.
    PoolInfo[] public poolInfo;

    // Info of each user that stakes LP tokens.
    mapping(uint256 => mapping(address => UserInfo)) public userInfo;
    // Pending rewards for each user in each pool (pending rewards accrued since last deposit/withdrawal)
    mapping(uint256 => mapping(address => uint256)) public pendingRewards;

    // Total allocation points. Must be the sum of all allocation points in all pools.
    uint256 public totalAllocPoint = 0;

    // The time when SHARE mining starts.
    uint256 public poolStartTime;

    // The time when SHARE mining ends.
    uint256 public poolEndTime;
    uint256 public sharePerSecond = 0 ether;
    uint256 public runningTime = 30 days;

    event Deposit(address indexed user, uint256 indexed pid, uint256 amount);
    event Withdraw(address indexed user, uint256 indexed pid, uint256 amount);
    event EmergencyWithdraw(address indexed user, uint256 indexed pid, uint256 amount);
    event RewardPaid(address indexed user, uint256 amount);

    constructor(
        address _share,
        address _bribesSafe,
        uint256 _poolStartTime,
        address _shadowVoter,
        address _swapxVoter
    ) {
        require(block.timestamp < _poolStartTime, "pool cant be started in the past");
        if (_share != address(0)) share = IERC20(_share);
        if(_bribesSafe != address(0)) bribesSafe = _bribesSafe;

        poolStartTime = _poolStartTime;
        poolEndTime = _poolStartTime + runningTime;
        operator = msg.sender;
        shadowVoter = IShadowVoter(_shadowVoter);
        swapxVoter = ISwapxVoter(_swapxVoter);
        bribesSafe = _bribesSafe;
        msigWallet = _bribesSafe;

        // create the LP pools
        add(0.000578010052004059 ether, 0, IERC20(0xfB5C6a1232AA36FE9982FDab18C1988B3e653662), false, 0); // BILL-S
        add(0.000358399923896499 ether, 0, IERC20(0x3914D28997764C21545f5E456928A824a73D7Ea3), false, 0); // SHARE-S

    }

    modifier onlyOperator() {
        require(operator == msg.sender, "ShareRewardPool: caller is not the operator");
        _;
    }

    function poolLength() external view returns (uint256) {
        return poolInfo.length;
    }

    function checkPoolDuplicate(IERC20 _token) internal view {
        uint256 length = poolInfo.length;
        for (uint256 pid = 0; pid < length; ++pid) {
            require(poolInfo[pid].token != _token, "ShareRewardPool: existing pool");
        }
    }

    // Add new lp to the pool. Can only be called by operator.
    function add(
        uint256 _allocPoint,
        uint256 _depFee,
        IERC20 _token,
        bool _withUpdate,
        uint256 _lastRewardTime
    ) public onlyOperator {
        checkPoolDuplicate(_token);
        if (_withUpdate) {
            massUpdatePools();
        }
        if (block.timestamp < poolStartTime) {
            if (_lastRewardTime == 0) {
                _lastRewardTime = poolStartTime;
            } else {
                if (_lastRewardTime < poolStartTime) {
                    _lastRewardTime = poolStartTime;
                }
            }
        } else {
            if (_lastRewardTime == 0 || _lastRewardTime < block.timestamp) {
                _lastRewardTime = block.timestamp;
            }
        }
        bool _isStarted = (_lastRewardTime <= poolStartTime) || (_lastRewardTime <= block.timestamp);
        poolInfo.push(PoolInfo({
            token: _token,
            depFee: _depFee,
            allocPoint: _allocPoint,
            poolSharePerSec: _allocPoint,
            lastRewardTime: _lastRewardTime,
            accSharePerShare: 0,
            isStarted: _isStarted,
            gaugeInfo: GaugeInfo(false, address(0), GaugeDex.NONE)
        }));
        
        if (_isStarted) {
            totalAllocPoint = totalAllocPoint.add(_allocPoint);
            sharePerSecond = sharePerSecond.add(_allocPoint);
        }
    }

    // Update the given pool's SHARE allocation point. Can only be called by the operator.
    function set(uint256 _pid, uint256 _allocPoint, uint256 _depFee) public onlyOperator {
        massUpdatePools();

        PoolInfo storage pool = poolInfo[_pid];
        require(_depFee < 200);  // deposit fee cant be more than 2%;
        pool.depFee = _depFee;

        if (pool.isStarted) {
            totalAllocPoint = totalAllocPoint.sub(pool.allocPoint).add(_allocPoint);
            sharePerSecond = sharePerSecond.sub(pool.poolSharePerSec).add(_allocPoint);
        }
        pool.allocPoint = _allocPoint;
        pool.poolSharePerSec = _allocPoint;
    }

    function bulkSet(uint256[] calldata _pids, uint256[] calldata _allocPoints, uint256[] calldata _depFees) external onlyOperator {
        require(_pids.length == _allocPoints.length && _pids.length == _depFees.length, "ShareRewardPool: invalid length");
        for (uint256 i = 0; i < _pids.length; i++) {
            set(_pids[i], _allocPoints[i], _depFees[i]);
        }
    }

    // Return accumulate rewards over the given _from to _to block.
    function getGeneratedReward(uint256 _fromTime, uint256 _toTime) public view returns (uint256) {
        if (_fromTime >= _toTime) return 0;
        if (_toTime >= poolEndTime) {
            if (_fromTime >= poolEndTime) return 0;
            if (_fromTime <= poolStartTime) return poolEndTime.sub(poolStartTime).mul(sharePerSecond);
            return poolEndTime.sub(_fromTime).mul(sharePerSecond);
        } else {
            if (_toTime <= poolStartTime) return 0;
            if (_fromTime <= poolStartTime) return _toTime.sub(poolStartTime).mul(sharePerSecond);
            return _toTime.sub(_fromTime).mul(sharePerSecond);
        }
    }

    // View function to see pending SHAREs on frontend.
    function pendingShare(uint256 _pid, address _user) public view returns (uint256) {
        PoolInfo storage pool = poolInfo[_pid];
        UserInfo storage user = userInfo[_pid][_user];
        uint256 accSharePerShare = pool.accSharePerShare;
        uint256 tokenSupply = pool.gaugeInfo.isGauge ? IShadowGauge(pool.gaugeInfo.gauge).balanceOf(address(this)) : pool.token.balanceOf(address(this));
        if (block.timestamp > pool.lastRewardTime && tokenSupply != 0) {
            uint256 _generatedReward = getGeneratedReward(pool.lastRewardTime, block.timestamp);
            uint256 _shareReward = _generatedReward.mul(pool.allocPoint).div(totalAllocPoint);
            accSharePerShare = accSharePerShare.add(_shareReward.mul(1e18).div(tokenSupply));
        }
        return user.amount.mul(accSharePerShare).div(1e18).sub(user.rewardDebt);
    }

    // View function to see pending SHAREs on frontend and any other pending rewards accumulated.
    function pendingShareAndPendingRewards(uint256 _pid, address _user) external view returns (uint256) {
        uint256 _pendingShare = pendingShare(_pid, _user);
        return _pendingShare.add(pendingRewards[_pid][_user]);
    }

    function massUpdatePools() public {
        uint256 length = poolInfo.length;
        for (uint256 pid = 0; pid < length; ++pid) {
            updatePool(pid);
            updatePoolWithGaugeDeposit(pid);
        }
    }

    // massUpdatePoolsInRange
    function massUpdatePoolsInRange(uint256 _fromPid, uint256 _toPid) public {
        require(_fromPid <= _toPid, "ShareRewardPool: invalid range");
        for (uint256 pid = _fromPid; pid <= _toPid; ++pid) {
            updatePool(pid);
            updatePoolWithGaugeDeposit(pid);
        }
    }

    // Update reward variables of the given pool to be up-to-date.
    function updatePool(uint256 _pid) private {
        updatePoolWithGaugeDeposit(_pid);
        PoolInfo storage pool = poolInfo[_pid];
        if (block.timestamp <= pool.lastRewardTime) {
            return;
        }
        uint256 tokenSupply = pool.gaugeInfo.isGauge ? IShadowGauge(pool.gaugeInfo.gauge).balanceOf(address(this)) : pool.token.balanceOf(address(this));
        if (tokenSupply == 0) {
            pool.lastRewardTime = block.timestamp;
            return;
        }
        if (!pool.isStarted) {
            pool.isStarted = true;
            totalAllocPoint = totalAllocPoint.add(pool.allocPoint);
            sharePerSecond = sharePerSecond.add(pool.poolSharePerSec);
        }
        if (totalAllocPoint > 0) {
            uint256 _generatedReward = getGeneratedReward(pool.lastRewardTime, block.timestamp);
            uint256 _shareReward = _generatedReward.mul(pool.allocPoint).div(totalAllocPoint);
            pool.accSharePerShare = pool.accSharePerShare.add(_shareReward.mul(1e18).div(tokenSupply));
        }
        pool.lastRewardTime = block.timestamp;
        if (claimGaugeRewardsOnUpdatePool) {claimGaugeRewards(_pid);}
    }
    
    // Deposit LP tokens to earn rewards
    function updatePoolWithGaugeDeposit(uint256 _pid) public {
        PoolInfo storage pool = poolInfo[_pid];
        address gauge = pool.gaugeInfo.gauge;
        uint256 balance = pool.token.balanceOf(address(this));
        // Do nothing if this pool doesn't have a gauge
        if (pool.gaugeInfo.isGauge) {
            // Do nothing if the LP token in the MC is empty
            if (balance > 0) {
                // Approve to the gauge
                if (pool.token.allowance(address(this), gauge) < balance ){
                    pool.token.approve(gauge, type(uint256).max);
                }
                // Deposit the LP in the gauge
                IShadowGauge(pool.gaugeInfo.gauge).deposit(balance); // NOTE: no need to check if gauge is shadow or swapx, because both have the same function
            }
        }
    }

    // Claim rewards to treasury
    function claimGaugeRewards(uint256 _pid) public {
        PoolInfo storage pool = poolInfo[_pid];
        if (pool.gaugeInfo.isGauge) {
            if (pool.gaugeInfo.gaugeDex == GaugeDex.SHADOW) {
                _claimShadowRewards(_pid);
            }
            if (pool.gaugeInfo.gaugeDex == GaugeDex.SWAPX) { 
                _claimSwapxRewards(_pid);
            }
        }
    }

    function claimAllFarmRewards() public onlyOperator {
        uint256 length = poolInfo.length;
        for (uint256 pid = 0; pid < length; ++pid) {
            claimGaugeRewards(pid);
        }
    }

    function _claimShadowRewards(uint256 _pid) internal {
        PoolInfo storage pool = poolInfo[_pid];
        address[] memory gaugeRewardTokens = IShadowGauge(pool.gaugeInfo.gauge).rewardsList();
        IShadowGauge(pool.gaugeInfo.gauge).getReward(address(this), gaugeRewardTokens);

        for (uint256 i = 0; i < gaugeRewardTokens.length; i++) {
            IERC20 rewardToken = IERC20(gaugeRewardTokens[i]);
            uint256 rewardAmount = rewardToken.balanceOf(address(this));

            if (rewardAmount > 0) {
                if (address(rewardToken) == XSHADOW_TOKEN) {
                    if (mustConvertXShadow) {
                        _convertXShadow(rewardAmount);
                    }
                } else {
                    rewardToken.safeTransfer(bribesSafe, rewardAmount);
                }
            }
        }
    }

    function _convertXShadow(uint256 _amount) internal {
        IERC20(XSHADOW_TOKEN).approve(address(X33_TOKEN), _amount); // approve xshadow to x33
        bool canMint = IX33(X33_TOKEN).isUnlocked();
        if (canMint) {
            uint256 x33ReceivedAmount = IERC4626(X33_WRAPPER).deposit(_amount, address(this)); // mint x33
            IERC20(X33_TOKEN).safeTransfer(bribesSafe, x33ReceivedAmount); // send x33 to bribesSafe
        }
    }

    function convertXShadowManual(uint256 _amount, bool _auto) public onlyOperator {
        IERC20(XSHADOW_TOKEN).approve(address(X33_TOKEN), _amount); // approve xshadow to x33
        bool canMint = IX33(X33_TOKEN).isUnlocked();
        if (canMint) {
            if (_auto) {
                uint256 x33ReceivedAmount = IERC4626(X33_WRAPPER).deposit(_amount, address(this)); // mint x33
                IERC20(X33_TOKEN).safeTransfer(bribesSafe, x33ReceivedAmount); // send x33 to bribesSafe
            } else {
                IERC4626(X33_WRAPPER).deposit(_amount, address(this)); // mint x33
                IERC20(X33_TOKEN).safeTransfer(bribesSafe, _amount); // send x33 to bribesSafe
            }
        }
    }

    function _claimSwapxRewards(uint256 _pid) internal {
        PoolInfo storage pool = poolInfo[_pid];
        ISwapxGauge(pool.gaugeInfo.gauge).getReward(); // claim the swapx rewards

        IERC20 rewardToken = IERC20(SWAPX_TOKEN);
        uint256 rewardAmount = rewardToken.balanceOf(address(this));
        if (rewardAmount > 0) {
            rewardToken.safeTransfer(bribesSafe, rewardAmount);
        }
    }

    // Add a gauge to a pool
    function enableGauge(uint256 _pid, GaugeDex _gaugeDex) public onlyOperator {
        if (_gaugeDex == GaugeDex.SHADOW) {
            _enableGaugeShadow(_pid);
        }
        if (_gaugeDex == GaugeDex.SWAPX) {
            _enableGaugeSwapX(_pid);
        }
    }

    function _enableGaugeShadow(uint256 _pid) internal {
        address gauge = shadowVoter.gaugeForPool(address(poolInfo[_pid].token));
        if (gauge != address(0)) {
            poolInfo[_pid].gaugeInfo = GaugeInfo(true, gauge, GaugeDex.SHADOW);
        }
    }

    function _enableGaugeSwapX(uint256 _pid) internal {
        // Add the logic for swapx
        address gauge = swapxVoter.gauges(address(poolInfo[_pid].token));
        if (gauge != address(0)) {
            poolInfo[_pid].gaugeInfo = GaugeInfo(true, gauge, GaugeDex.SWAPX);
        }
    }

    // Withdraw LP from the gauge
    function withdrawFromGauge(uint256 _pid, uint256 _amount) internal {
        PoolInfo storage pool = poolInfo[_pid];
        // Do nothing if this pool doesn't have a gauge
        if (pool.gaugeInfo.isGauge) {
            // Withdraw from the gauge
            IShadowGauge(pool.gaugeInfo.gauge).withdraw(_amount); 
        }
    }

    // Deposit tokens.
    function deposit(uint256 _pid, uint256 _amount) public nonReentrant {
        address _sender = msg.sender;
        PoolInfo storage pool = poolInfo[_pid];
        UserInfo storage user = userInfo[_pid][_sender];
        updatePool(_pid);
        if (user.amount > 0) {
            uint256 _pending = user.amount.mul(pool.accSharePerShare).div(1e18).sub(user.rewardDebt);
            if (_pending > 0) {
                // accrue pending rewards to be claimed later
                pendingRewards[_pid][_sender] = pendingRewards[_pid][_sender].add(_pending);
            }
        }
        if (_amount > 0 ) {
            pool.token.safeTransferFrom(_sender, address(this), _amount);
            uint256 depositDebt = _amount.mul(pool.depFee).div(10000);
            user.amount = user.amount.add(_amount.sub(depositDebt));
            pool.token.safeTransfer(bribesSafe, depositDebt);
        }
        updatePoolWithGaugeDeposit(_pid);
        user.rewardDebt = user.amount.mul(pool.accSharePerShare).div(1e18);
        emit Deposit(_sender, _pid, _amount);
    }

    // Withdraw tokens.
    function withdraw(uint256 _pid, uint256 _amount) public payable nonReentrant {
        address _sender = msg.sender;
        PoolInfo storage pool = poolInfo[_pid];
        UserInfo storage user = userInfo[_pid][_sender];
        require(user.amount >= _amount, "withdraw: not good");
        updatePool(_pid);
        updatePoolWithGaugeDeposit(_pid);
        uint256 _pending = user.amount.mul(pool.accSharePerShare).div(1e18).sub(user.rewardDebt);
        if (_pending > 0) {
            // accrue pending rewards to be claimed later
            pendingRewards[_pid][_sender] = pendingRewards[_pid][_sender].add(_pending);
        }
        if (_amount > 0) {
            user.amount = user.amount.sub(_amount);
            withdrawFromGauge(_pid, _amount);
            pool.token.safeTransfer(_sender, _amount);
        }
        user.rewardDebt = user.amount.mul(pool.accSharePerShare).div(1e18);
        emit Withdraw(_sender, _pid, _amount);
    }

    function harvest(uint256 _pid) public payable nonReentrant { 
        address _sender = msg.sender;
        PoolInfo storage pool = poolInfo[_pid];
        UserInfo storage user = userInfo[_pid][_sender];

        // Ensure rewards are updated
        updatePool(_pid);
        updatePoolWithGaugeDeposit(_pid);

        // Calculate the latest pending rewards
        uint256 _pending = user.amount.mul(pool.accSharePerShare).div(1e18).sub(user.rewardDebt);
        uint256 _accumulatedPending = pendingRewards[_pid][_sender];
        uint256 _rewardsToClaim = _pending.add(_accumulatedPending);

        // Ensure that the user is claiming an amount above the minimum threshold
        require(_rewardsToClaim >= minClaimThreshold, "Claim amount below minimum threshold");

        if (_rewardsToClaim > 0) {
            pendingRewards[_pid][_sender] = 0;

            uint256 amountSonicToPay = 0;
            if (pegStabilityModuleFeeEnabled) {
                uint256 currentSHAREPriceInSonic = shareOracle.twap(address(share), 1e18);
                amountSonicToPay = (currentSHAREPriceInSonic.mul(_rewardsToClaim).div(1e18)).mul(pegStabilityModuleFee).div(1000);
                require(msg.value >= amountSonicToPay, "insufficient sonic for PSM cost");
            } else {
                require(msg.value == 0, "ShareRewardPool: invalid msg.value");
            }

            safeShareTransfer(_sender, _rewardsToClaim);
            emit RewardPaid(_sender, _rewardsToClaim);

            // Refund any excess S if pegStabilityModuleFee is enabled
            if (pegStabilityModuleFeeEnabled && msg.value > amountSonicToPay) {
                uint256 refundAmount = msg.value - amountSonicToPay;
                (bool success, ) = _sender.call{value: refundAmount}("");
                require(success, "Refund failed");
            }
        }
        // Update the user’s reward debt
        user.rewardDebt = user.amount.mul(pool.accSharePerShare).div(1e18);
    }

    function harvestAll() public payable nonReentrant {
        address _sender = msg.sender;
        uint256 length = poolInfo.length;
        uint256 totalUserRewardsToClaim = 0;

        for (uint256 pid = 0; pid < length; ++pid) {
            PoolInfo storage pool = poolInfo[pid];
            UserInfo storage user = userInfo[pid][_sender];

            // Ensure rewards are updated
            updatePool(pid);
            updatePoolWithGaugeDeposit(pid);

            // Calculate the latest pending rewards
            uint256 _pending = user.amount.mul(pool.accSharePerShare).div(1e18).sub(user.rewardDebt);
            uint256 _accumulatedPending = pendingRewards[pid][_sender];
            uint256 _rewardsToClaim = _pending.add(_accumulatedPending);

            if (_rewardsToClaim > 0) {
                pendingRewards[pid][_sender] = 0;
                totalUserRewardsToClaim = totalUserRewardsToClaim.add(_rewardsToClaim);
            }
            // Update the user’s reward debt
            user.rewardDebt = user.amount.mul(pool.accSharePerShare).div(1e18);
        }

        // Ensure that the user is claiming an amount above the minimum threshold
        require(totalUserRewardsToClaim >= minClaimThreshold, "Claim amount below minimum threshold");

        if (totalUserRewardsToClaim > 0) {
            uint256 amountSonicToPay = 0;
            if (pegStabilityModuleFeeEnabled) {
                uint256 currentSHAREPriceInSonic = shareOracle.twap(address(share), 1e18);
                amountSonicToPay = (currentSHAREPriceInSonic.mul(totalUserRewardsToClaim).div(1e18)).mul(pegStabilityModuleFee).div(1000);
                require(msg.value >= amountSonicToPay, "insufficient sonic for PSM cost");
            } else {
                require(msg.value == 0, "ShareRewardPool: invalid msg.value");
            }

            safeShareTransfer(_sender, totalUserRewardsToClaim);
            emit RewardPaid(_sender, totalUserRewardsToClaim);

            // Refund any excess S if pegStabilityModuleFee is enabled
            if (pegStabilityModuleFeeEnabled && msg.value > amountSonicToPay) {
                uint256 refundAmount = msg.value - amountSonicToPay;
                (bool success, ) = _sender.call{value: refundAmount}("");
                require(success, "Refund failed");
            }
        }
    }

    // claim and withdraw
    function exitFarm(uint256 _pid) public payable nonReentrant { 
        harvest(_pid);
        emergencyWithdraw(_pid);
    }

    // Withdraw without caring about rewards. EMERGENCY ONLY.
    function emergencyWithdraw(uint256 _pid) public nonReentrant {
        PoolInfo storage pool = poolInfo[_pid];
        UserInfo storage user = userInfo[_pid][msg.sender];
        uint256 _amount = user.amount;
        withdrawFromGauge(_pid, _amount);
        pendingRewards[_pid][msg.sender] = 0;
        user.amount = 0;
        user.rewardDebt = 0;
        pool.token.safeTransfer(msg.sender, _amount);
        emit EmergencyWithdraw(msg.sender, _pid, _amount);
    }

    // Safe share transfer function, just in case if rounding error causes pool to not have enough SHAREs.
    function safeShareTransfer(address _to, uint256 _amount) internal {
        uint256 _shareBal = share.balanceOf(address(this));
        if (_shareBal > 0) {
            if (_amount > _shareBal) {
                share.safeTransfer(_to, _shareBal);
            } else {
                share.safeTransfer(_to, _amount);
            }
        }
    }

    function setOperator(address _operator) external onlyOperator {
        operator = _operator;
    }

    function setBribesSafe(address _bribesSafe) public onlyOperator {
        bribesSafe = _bribesSafe;
    }

    function setMsigWallet(address _msigWallet) public onlyOperator {
        msigWallet = _msigWallet;
    }

    function setPegStabilityModuleFee(uint256 _pegStabilityModuleFee) external onlyOperator {
        require(_pegStabilityModuleFee <= 500, "ShareRewardPool: invalid peg stability module fee"); // max 50%
        pegStabilityModuleFee = _pegStabilityModuleFee;
    }

    function setMustConvertXShadow(bool _mustConvertXShadow) external onlyOperator {
        mustConvertXShadow = _mustConvertXShadow;
    }

    function setShareOracle(IOracle _shareOracle) external onlyOperator {
        shareOracle = _shareOracle;
    }

    function setPegStabilityModuleFeeEnabled(bool _enabled) external onlyOperator {
        pegStabilityModuleFeeEnabled = _enabled;
    }

    function setMinClaimThreshold(uint256 _minClaimThreshold) external onlyOperator {
        require(_minClaimThreshold >= 0, "ShareRewardPool: invalid min claim threshold");
        require(_minClaimThreshold <= 1e18, "ShareRewardPool: invalid max claim threshold");
        minClaimThreshold = _minClaimThreshold;
    }

    function setClaimGaugeRewardsOnUpdatePool(bool _claimGaugeRewardsOnUpdatePool) external onlyOperator {
        claimGaugeRewardsOnUpdatePool = _claimGaugeRewardsOnUpdatePool;
    }

    function governanceRecoverUnsupported(IERC20 _token, uint256 amount, address to) external onlyOperator {
        uint256 length = poolInfo.length;
        for (uint256 pid = 0; pid < length; ++pid) {
            PoolInfo storage pool = poolInfo[pid];
            require(_token != pool.token, "ShareRewardPool: Token cannot be pool token");
        }
        _token.safeTransfer(to, amount);
    }

    /**
     * @notice Collects the Sonic.
     * @param amount The amount of Sonic to collect
     */

    function collectSonic(uint256 amount) public onlyOperator {
        (bool sent,) = bribesSafe.call{value: amount}("");
        require(sent, "failed to send Sonic");
    }

    function collectSonicMsig(uint256 amount) public onlyOperator {
        (bool sent,) = msigWallet.call{value: amount}("");
        require(sent, "failed to send Sonic");
    }
}