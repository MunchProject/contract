// SPDX-License-Identifier: MIT
/*
MUNCH PROJECT                                                                                                                                                               
website: https://www.munchproject.io
telegram: https://t.me/MUNCHProjectportal
twitter: https://x.com/munchtoken
*/

pragma solidity ^0.8.19;

import "@openzeppelin/contracts/access/Ownable.sol";
import "@uniswap/v2-periphery/contracts/interfaces/IUniswapV2Router02.sol";
import "@uniswap/v2-core/contracts/interfaces/IUniswapV2Factory.sol";
import "@openzeppelin/contracts/utils/ReentrancyGuard.sol";

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
    event Approval(
        address indexed owner,
        address indexed spender,
        uint256 value
    );

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
    function allowance(
        address owner,
        address spender
    ) external view returns (uint256);

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
    function transferFrom(
        address from,
        address to,
        uint256 amount
    ) external returns (bool);
}

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

contract ERC20 is Context, IERC20, IERC20Metadata {
    mapping(address => uint256) private _balances;

    mapping(address => mapping(address => uint256)) private _allowances;

    uint256 private _totalSupply;

    string private _name;
    string private _symbol;

    /**
     * @dev Sets the values for {name} and {symbol}.
     *
     * All two of these values are immutable: they can only be set once during
     * construction.
     */
    constructor(string memory name_, string memory symbol_) {
        _name = name_;
        _symbol = symbol_;
    }

    /**
     * @dev Returns the name of the token.
     */
    function name() public view virtual override returns (string memory) {
        return _name;
    }

    /**
     * @dev Returns the symbol of the token, usually a shorter version of the
     * name.
     */
    function symbol() public view virtual override returns (string memory) {
        return _symbol;
    }

    /**
     * @dev Returns the number of decimals used to get its user representation.
     * For example, if `decimals` equals `2`, a balance of `505` tokens should
     * be displayed to a user as `5.05` (`505 / 10 ** 2`).
     *
     * Tokens usually opt for a value of 18, imitating the relationship between
     * Ether and Wei. This is the default value returned by this function, unless
     * it's overridden.
     *
     * NOTE: This information is only used for _display_ purposes: it in
     * no way affects any of the arithmetic of the contract, including
     * {IERC20-balanceOf} and {IERC20-transfer}.
     */
    function decimals() public view virtual override returns (uint8) {
        return 18;
    }

    /**
     * @dev See {IERC20-totalSupply}.
     */
    function totalSupply() public view virtual override returns (uint256) {
        return _totalSupply;
    }

    /**
     * @dev See {IERC20-balanceOf}.
     */
    function balanceOf(
        address account
    ) public view virtual override returns (uint256) {
        return _balances[account];
    }

    /**
     * @dev See {IERC20-transfer}.
     *
     * Requirements:
     *
     * - `to` cannot be the zero address.
     * - the caller must have a balance of at least `amount`.
     */
    function transfer(
        address to,
        uint256 amount
    ) public virtual override returns (bool) {
        address owner = _msgSender();
        _transfer(owner, to, amount);
        return true;
    }

    /**
     * @dev See {IERC20-allowance}.
     */
    function allowance(
        address owner,
        address spender
    ) public view virtual override returns (uint256) {
        return _allowances[owner][spender];
    }

    /**
     * @dev See {IERC20-approve}.
     *
     * NOTE: If `amount` is the maximum `uint256`, the allowance is not updated on
     * `transferFrom`. This is semantically equivalent to an infinite approval.
     *
     * Requirements:
     *
     * - `spender` cannot be the zero address.
     */
    function approve(
        address spender,
        uint256 amount
    ) public virtual override returns (bool) {
        address owner = _msgSender();
        _approve(owner, spender, amount);
        return true;
    }

    /**
     * @dev See {IERC20-transferFrom}.
     *
     * Emits an {Approval} event indicating the updated allowance. This is not
     * required by the EIP. See the note at the beginning of {ERC20}.
     *
     * NOTE: Does not update the allowance if the current allowance
     * is the maximum `uint256`.
     *
     * Requirements:
     *
     * - `from` and `to` cannot be the zero address.
     * - `from` must have a balance of at least `amount`.
     * - the caller must have allowance for ``from``'s tokens of at least
     * `amount`.
     */
    function transferFrom(
        address from,
        address to,
        uint256 amount
    ) public virtual override returns (bool) {
        address spender = _msgSender();
        _spendAllowance(from, spender, amount);
        _transfer(from, to, amount);
        return true;
    }

    /**
     * @dev Atomically increases the allowance granted to `spender` by the caller.
     *
     * This is an alternative to {approve} that can be used as a mitigation for
     * problems described in {IERC20-approve}.
     *
     * Emits an {Approval} event indicating the updated allowance.
     *
     * Requirements:
     *
     * - `spender` cannot be the zero address.
     */
    function increaseAllowance(
        address spender,
        uint256 addedValue
    ) public virtual returns (bool) {
        address owner = _msgSender();
        _approve(owner, spender, allowance(owner, spender) + addedValue);
        return true;
    }

    /**
     * @dev Atomically decreases the allowance granted to `spender` by the caller.
     *
     * This is an alternative to {approve} that can be used as a mitigation for
     * problems described in {IERC20-approve}.
     *
     * Emits an {Approval} event indicating the updated allowance.
     *
     * Requirements:
     *
     * - `spender` cannot be the zero address.
     * - `spender` must have allowance for the caller of at least
     * `subtractedValue`.
     */
    function decreaseAllowance(
        address spender,
        uint256 subtractedValue
    ) public virtual returns (bool) {
        address owner = _msgSender();
        uint256 currentAllowance = allowance(owner, spender);
        require(
            currentAllowance >= subtractedValue,
            "ERC20: decreased allowance below zero"
        );
        unchecked {
            _approve(owner, spender, currentAllowance - subtractedValue);
        }

        return true;
    }

    /**
     * @dev Moves `amount` of tokens from `from` to `to`.
     *
     * This internal function is equivalent to {transfer}, and can be used to
     * e.g. implement automatic token fees, slashing mechanisms, etc.
     *
     * Emits a {Transfer} event.
     *
     * Requirements:
     *
     * - `from` cannot be the zero address.
     * - `to` cannot be the zero address.
     * - `from` must have a balance of at least `amount`.
     */
    function _transfer(
        address from,
        address to,
        uint256 amount
    ) internal virtual {
        require(from != address(0), "ERC20: transfer from the zero address");
        require(to != address(0), "ERC20: transfer to the zero address");

        _beforeTokenTransfer(from, to, amount);

        uint256 fromBalance = _balances[from];
        require(
            fromBalance >= amount,
            "ERC20: transfer amount exceeds balance"
        );
        unchecked {
            _balances[from] = fromBalance - amount;
            // Overflow not possible: the sum of all balances is capped by totalSupply, and the sum is preserved by
            // decrementing then incrementing.
            _balances[to] += amount;
        }

        emit Transfer(from, to, amount);

        _afterTokenTransfer(from, to, amount);
    }

    /** @dev Creates `amount` tokens and assigns them to `account`, increasing
     * the total supply.
     *
     * Emits a {Transfer} event with `from` set to the zero address.
     *
     * Requirements:
     *
     * - `account` cannot be the zero address.
     */
    function _mint(address account, uint256 amount) internal virtual {
        require(account != address(0), "ERC20: mint to the zero address");

        _beforeTokenTransfer(address(0), account, amount);

        _totalSupply += amount;
        unchecked {
            // Overflow not possible: balance + amount is at most totalSupply + amount, which is checked above.
            _balances[account] += amount;
        }
        emit Transfer(address(0), account, amount);

        _afterTokenTransfer(address(0), account, amount);
    }

    /**
     * @dev Destroys `amount` tokens from `account`, reducing the
     * total supply.
     *
     * Emits a {Transfer} event with `to` set to the zero address.
     *
     * Requirements:
     *
     * - `account` cannot be the zero address.
     * - `account` must have at least `amount` tokens.
     */
    function _burn(address account, uint256 amount) internal virtual {
        require(account != address(0), "ERC20: burn from the zero address");

        _beforeTokenTransfer(account, address(0), amount);

        uint256 accountBalance = _balances[account];
        require(accountBalance >= amount, "ERC20: burn amount exceeds balance");
        unchecked {
            _balances[account] = accountBalance - amount;
            // Overflow not possible: amount <= accountBalance <= totalSupply.
            _totalSupply -= amount;
        }

        emit Transfer(account, address(0), amount);

        _afterTokenTransfer(account, address(0), amount);
    }

    /**
     * @dev Sets `amount` as the allowance of `spender` over the `owner` s tokens.
     *
     * This internal function is equivalent to `approve`, and can be used to
     * e.g. set automatic allowances for certain subsystems, etc.
     *
     * Emits an {Approval} event.
     *
     * Requirements:
     *
     * - `owner` cannot be the zero address.
     * - `spender` cannot be the zero address.
     */
    function _approve(
        address owner,
        address spender,
        uint256 amount
    ) internal virtual {
        require(owner != address(0), "ERC20: approve from the zero address");
        require(spender != address(0), "ERC20: approve to the zero address");

        _allowances[owner][spender] = amount;
        emit Approval(owner, spender, amount);
    }

    /**
     * @dev Updates `owner` s allowance for `spender` based on spent `amount`.
     *
     * Does not update the allowance amount in case of infinite allowance.
     * Revert if not enough allowance is available.
     *
     * Might emit an {Approval} event.
     */
    function _spendAllowance(
        address owner,
        address spender,
        uint256 amount
    ) internal virtual {
        uint256 currentAllowance = allowance(owner, spender);
        if (currentAllowance != type(uint256).max) {
            require(
                currentAllowance >= amount,
                "ERC20: insufficient allowance"
            );
            unchecked {
                _approve(owner, spender, currentAllowance - amount);
            }
        }
    }

    /**
     * @dev Hook that is called before any transfer of tokens. This includes
     * minting and burning.
     *
     * Calling conditions:
     *
     * - when `from` and `to` are both non-zero, `amount` of ``from``'s tokens
     * will be transferred to `to`.
     * - when `from` is zero, `amount` tokens will be minted for `to`.
     * - when `to` is zero, `amount` of ``from``'s tokens will be burned.
     * - `from` and `to` are never both zero.
     *
     * To learn more about hooks, head to xref:ROOT:extending-contracts.adoc#using-hooks[Using Hooks].
     */
    function _beforeTokenTransfer(
        address from,
        address to,
        uint256 amount
    ) internal virtual {}

    /**
     * @dev Hook that is called after any transfer of tokens. This includes
     * minting and burning.
     *
     * Calling conditions:
     *
     * - when `from` and `to` are both non-zero, `amount` of ``from``'s tokens
     * has been transferred to `to`.
     * - when `from` is zero, `amount` tokens have been minted for `to`.
     * - when `to` is zero, `amount` of ``from``'s tokens have been burned.
     * - `from` and `to` are never both zero.
     *
     * To learn more about hooks, head to xref:ROOT:extending-contracts.adoc#using-hooks[Using Hooks].
     */
    function _afterTokenTransfer(
        address from,
        address to,
        uint256 amount
    ) internal virtual {}
}

contract MunchToken is ReentrancyGuard, ERC20, Ownable {
    // ================ Variables ================

    IUniswapV2Router02 public immutable uniswapV2Router;
    address public uniswapV2Pair;

    address public treasuryWallet;
    address public donationWallet;
    address public communityWallet;
    address public constant deadAddress = address(0xdead);

    bool public swapEnabled;
    bool private _swapping;

    uint256 public maxTransaction;
    uint256 public maxWallet;
    uint256 public swapTokensAtAmount;

    uint256 public buyTotalFees;
    uint256 private _buyTreasuryFee;
    uint256 private _buyDonationFee;
    uint256 private _buyCommunityFee;

    uint256 public sellTotalFees;
    uint256 private _sellTreasuryFee;
    uint256 private _sellDonationFee;
    uint256 private _sellCommunityFee;

    uint256 private _tokensForTreasury;
    uint256 private _tokensForDonation;
    uint256 private _tokensForCommunity;

    mapping(address => bool) private _isExcludedFromFees;
    mapping(address => bool) private _isExcludedFromMaxTransaction;
    mapping(address => bool) private _automatedMarketMakerPairs;

    // ================ Events ================
    event ExcludeFromLimits(address indexed account, bool isExcluded);

    event ExcludeFromFees(address indexed account, bool isExcluded);

    event SetAutomatedMarketMakerPair(address indexed pair, bool indexed value);

    event TreasuryWalletUpdated(
        address indexed newWallet,
        address indexed oldWallet
    );

    event DonationWalletUpdated(
        address indexed newWallet,
        address indexed oldWallet
    );

    event CommunityWalletUpdated(
        address indexed newWallet,
        address indexed oldWallet
    );

    event Swap(
        uint256 tokensSwapped,
        uint256 ethReceived,
        uint256 tokensIntoCommunity
    );

    event TokensAirdropped(uint256 totalWallets, uint256 totalTokens);

    event BuyFeesChanged(uint256 _treasuryFee, uint256 _donationFee, uint256 _communityFee);

    event SellFeesChanged(uint256 _treasuryFee, uint256 _donationFee, uint256 _communityFee);

    // ================ Constructor ================

    constructor() ERC20("Munch", "MUNCH") Ownable(_msgSender()) {
        uint256 totalSupply = 1_000_000_000 * (10 ** 18);

        address munchMultisig = 0xAC986861F21a807a88671554B604096142728C26;
        uniswapV2Router = IUniswapV2Router02(
            0x4752ba5DBc23f44D87826276BF6Fd6b1C372aD24 // base uniswap router
        );
        _approve(address(this), address(uniswapV2Router), type(uint256).max);
        uniswapV2Pair = IUniswapV2Factory(uniswapV2Router.factory()).createPair(
            address(this),
            uniswapV2Router.WETH()
        );

        maxTransaction = totalSupply;
        maxWallet = totalSupply / 100;
        swapTokensAtAmount = totalSupply / 4000;

        _buyTreasuryFee = 200;
        _buyDonationFee = 200;
        _buyCommunityFee = 100;
        buyTotalFees = _buyTreasuryFee + _buyDonationFee + _buyCommunityFee;

        _sellTreasuryFee = 200;
        _sellDonationFee = 200;
        _sellCommunityFee = 100;
        sellTotalFees = _sellTreasuryFee + _sellDonationFee + _sellCommunityFee;

        treasuryWallet = munchMultisig;
        donationWallet = munchMultisig;
        communityWallet = munchMultisig;

        swapEnabled = true;

        excludeFromFees(owner(), true);
        excludeFromFees(address(this), true);
        excludeFromFees(deadAddress, true);
        excludeFromFees(munchMultisig, true);

        excludeFromMaxTransaction(owner(), true);
        excludeFromMaxTransaction(address(this), true);
        excludeFromMaxTransaction(deadAddress, true);
        excludeFromMaxTransaction(address(uniswapV2Router), true);
        excludeFromMaxTransaction(munchMultisig, true);
        excludeFromMaxTransaction(address(uniswapV2Pair), true);
        _setAutomatedMarketMakerPair(address(uniswapV2Pair), true);

        _mint(owner(), totalSupply);
    }

    // ================ Public functions ================

    receive() external payable {}

    function burn(uint256 amount) public {
        _burn(msg.sender, amount);
    }

    function setSwapEnabled(bool value) public onlyOwner {
        swapEnabled = value;
    }

    function setSwapTokensAtAmount(uint256 amount) public onlyOwner {
        require(
            amount >= (totalSupply() * 1) / 100000,
            "ERC20: Swap amount cannot be lower than 0.001% total supply."
        );
        require(
            amount <= (totalSupply() * 5) / 1000,
            "ERC20: Swap amount cannot be higher than 0.5% total supply."
        );
        swapTokensAtAmount = amount;
    }

    function setMaxWalletAndMaxTransaction(
        uint256 _maxTransaction,
        uint256 _maxWallet
    ) public onlyOwner {
        require(
            _maxTransaction >= ((totalSupply() * 5) / 1000),
            "ERC20: Cannot set maxTxn lower than 0.5%"
        );
        require(
            _maxWallet >= ((totalSupply() * 5) / 1000),
            "ERC20: Cannot set maxWallet lower than 0.5%"
        );
        maxTransaction = _maxTransaction;
        maxWallet = _maxWallet;
    }

    function setBuyFees(
        uint256 _treasuryFee,
        uint256 _donationFee,
        uint256 _communityFee
    ) public onlyOwner {
        require(
            _treasuryFee + _donationFee + _communityFee <= 300,
            "ERC20: Must keep fees at 3% or less"
        );
        _buyTreasuryFee = _treasuryFee;
        _buyDonationFee = _donationFee;
        _buyCommunityFee = _communityFee;
        buyTotalFees = _buyTreasuryFee + _buyDonationFee + _buyCommunityFee;
        emit BuyFeesChanged(_treasuryFee, _donationFee, _communityFee);
    }

    function setSellFees(
        uint256 _treasuryFee,
        uint256 _donationFee,
        uint256 _communityFee
    ) public onlyOwner {
        require(
            _treasuryFee + _donationFee + _communityFee <= 300,
            "ERC20: Must keep fees at 3% or less"
        );
        _sellTreasuryFee = _treasuryFee;
        _sellDonationFee = _donationFee;
        _sellCommunityFee = _communityFee;
        sellTotalFees = _sellTreasuryFee + _sellDonationFee + _sellCommunityFee;
        emit SellFeesChanged(_treasuryFee, _donationFee, _communityFee);
    }

    function setTreasuryWallet(address _treasuryWallet) public onlyOwner {
        require(_treasuryWallet != address(0), "ERC20: Address 0");
        address oldWallet = treasuryWallet;
        treasuryWallet = _treasuryWallet;
        emit TreasuryWalletUpdated(treasuryWallet, oldWallet);
    }

    function setDonationWallet(address _donationWallet) public onlyOwner {
        require(_donationWallet != address(0), "ERC20: Address 0");
        address oldWallet = donationWallet;
        donationWallet = _donationWallet;
        emit DonationWalletUpdated(donationWallet, oldWallet);
    }

    function setCommunityWallet(address _communityWallet) public onlyOwner {
        require(_communityWallet != address(0), "ERC20: Address 0");
        address oldWallet = communityWallet;
        communityWallet = _communityWallet;
        emit CommunityWalletUpdated(communityWallet, oldWallet);
    }

    function excludeFromMaxTransaction(
        address account,
        bool value
    ) public onlyOwner {
        _isExcludedFromMaxTransaction[account] = value;
        emit ExcludeFromLimits(account, value);
    }

    function bulkExcludeFromMaxTransaction(
        address[] calldata accounts,
        bool value
    ) public onlyOwner {
        for (uint256 i = 0; i < accounts.length; i++) {
            _isExcludedFromMaxTransaction[accounts[i]] = value;
            emit ExcludeFromLimits(accounts[i], value);
        }
    }

    function excludeFromFees(address account, bool value) public onlyOwner {
        _isExcludedFromFees[account] = value;
        emit ExcludeFromFees(account, value);
    }

    function bulkExcludeFromFees(
        address[] calldata accounts,
        bool value
    ) public onlyOwner {
        for (uint256 i = 0; i < accounts.length; i++) {
            _isExcludedFromFees[accounts[i]] = value;
            emit ExcludeFromFees(accounts[i], value);
        }
    }

    function manualSwap() public onlyOwner {
        _swapTokensForETH(balanceOf(address(this)));
    }

    function withdrawStuckTokens(address tkn) public onlyOwner {
        bool success;
        if (tkn == address(0))
            (success, ) = address(msg.sender).call{
                value: address(this).balance
            }("");
        else {
            require(IERC20(tkn).balanceOf(address(this)) > 0, "No tokens");
            uint256 amount = IERC20(tkn).balanceOf(address(this));
            IERC20(tkn).transfer(msg.sender, amount);
        }
    }

    function airdrop(
        address[] calldata addresses,
        uint256[] calldata tokenAmounts
    ) external onlyOwner {
        require(addresses.length <= 250, "More than 250 wallets");
        require(
            addresses.length == tokenAmounts.length,
            "List length mismatch"
        );

        uint256 airdropTotal = 0;
        for (uint i = 0; i < addresses.length; i++) {
            airdropTotal += tokenAmounts[i];
        }
        require(balanceOf(msg.sender) >= airdropTotal, "Token balance too low");

        for (uint i = 0; i < addresses.length; i++) {
            super._transfer(msg.sender, addresses[i], tokenAmounts[i]);
        }

        emit TokensAirdropped(addresses.length, airdropTotal);
    }

    // ================ Internal functions ================

    function _transfer(
        address from,
        address to,
        uint256 amount
    ) internal override {
        require(from != address(0), "ERC20: transfer from the zero address");
        require(to != address(0), "ERC20: transfer to the zero address");

        if (amount == 0) {
            super._transfer(from, to, 0);
            return;
        }

        if (
            from != owner() &&
            to != owner() &&
            to != address(0) &&
            to != deadAddress &&
            !_swapping
        ) {
            //when buy
            if (
                _automatedMarketMakerPairs[from] &&
                !_isExcludedFromMaxTransaction[to]
            ) {
                require(
                    amount <= maxTransaction,
                    "ERC20: Buy transfer amount exceeds the maxTransaction."
                );
                require(
                    amount + balanceOf(to) <= maxWallet,
                    "ERC20: Max wallet exceeded"
                );
            }
            //when sell
            else if (
                _automatedMarketMakerPairs[to] &&
                !_isExcludedFromMaxTransaction[from]
            ) {
                require(
                    amount <= maxTransaction,
                    "ERC20: Sell transfer amount exceeds the maxTransaction."
                );
            } else if (!_isExcludedFromMaxTransaction[to]) {
                require(
                    amount + balanceOf(to) <= maxWallet,
                    "ERC20: Max wallet exceeded"
                );
            }
        }

        uint256 contractTokenBalance = balanceOf(address(this));

        bool canSwap = contractTokenBalance >= swapTokensAtAmount;

        if (
            canSwap &&
            swapEnabled &&
            !_swapping &&
            !_automatedMarketMakerPairs[from] &&
            !_isExcludedFromFees[from] &&
            !_isExcludedFromFees[to]
        ) {
            _swapping = true;

            _swapBack();

            _swapping = false;
        }

        bool takeFee = !_swapping;

        if (_isExcludedFromFees[from] || _isExcludedFromFees[to]) {
            takeFee = false;
        }

        uint256 fees = 0;

        if (takeFee) {
            // on sell
            if (_automatedMarketMakerPairs[to] && sellTotalFees > 0) {
                fees = amount * sellTotalFees / 10000;
                _tokensForCommunity +=
                    (fees * _sellCommunityFee) /
                    sellTotalFees;
                _tokensForTreasury += (fees * _sellTreasuryFee) / sellTotalFees;
                _tokensForDonation += (fees * _sellDonationFee) / sellTotalFees;
            }
            // on buy
            else if (_automatedMarketMakerPairs[from] && buyTotalFees > 0) {
                fees = amount * buyTotalFees / 10000;
                _tokensForCommunity += (fees * _buyCommunityFee) / buyTotalFees;
                _tokensForTreasury += (fees * _buyTreasuryFee) / buyTotalFees;
                _tokensForDonation += (fees * _buyDonationFee) / buyTotalFees;
            }

            if (fees > 0) {
                super._transfer(from, address(this), fees);
            }

            amount -= fees;
        }

        super._transfer(from, to, amount);
    }

    function _setAutomatedMarketMakerPair(address pair, bool value) internal {
        _automatedMarketMakerPairs[pair] = value;

        emit SetAutomatedMarketMakerPair(pair, value);
    }

    function _swapBack() internal {
        uint256 contractBalance = balanceOf(address(this));
        uint256 totalTokensToSwap = _tokensForCommunity +
            _tokensForTreasury +
            _tokensForDonation;
        bool success;

        if (contractBalance == 0 || totalTokensToSwap == 0) {
            return;
        }

        if (contractBalance > swapTokensAtAmount * 10) {
            contractBalance = swapTokensAtAmount * 10;
        }

        _swapTokensForETH(contractBalance);

        uint256 ethBalance = address(this).balance;

        uint256 ethForTreasury = ethBalance * _tokensForTreasury / totalTokensToSwap;

        uint256 ethForDonation = ethBalance * _tokensForDonation / totalTokensToSwap;

        _tokensForCommunity = 0;
        _tokensForTreasury = 0;
        _tokensForDonation = 0;

        (success, ) = address(donationWallet).call{value: ethForDonation}("");

        (success, ) = address(treasuryWallet).call{value: ethForTreasury}("");

        (success, ) = address(communityWallet).call{
            value: address(this).balance
        }("");
    }

    function _swapTokensForETH(uint256 tokenAmount) internal nonReentrant {
        address[] memory path = new address[](2);
        path[0] = address(this);
        path[1] = uniswapV2Router.WETH();

        _approve(address(this), address(uniswapV2Router), tokenAmount);

        // make the swap
        uniswapV2Router.swapExactTokensForETHSupportingFeeOnTransferTokens(
            tokenAmount,
            0,
            path,
            address(this),
            block.timestamp
        );
    }

    // ================ Views ================

    function isExcludedFromMaxTransaction(
        address account
    ) public view returns (bool) {
        return _isExcludedFromMaxTransaction[account];
    }

    function isExcludedFromFees(address account) public view returns (bool) {
        return _isExcludedFromFees[account];
    }
}
