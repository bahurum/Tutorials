// NOTE: I haven't rerun this yet!

methods {
    // balanceOf doesn't depend on msg.sender, block.timestamp, ...
    balanceOf(address) returns (uint256) envfree;
    allowance(address, address) returns (uint) envfree;
}


rule transferIncreasesRecipientBalance {
    address recipient; address sender; address anybody_else;
    uint amount;

    require sender != recipient;
    require anybody_else != sender;
    require anybody_else != recipient;

    mathint balance_sender_before = balanceOf(sender);
    mathint balance_recip_before  = balanceOf(recipient);
    mathint balance_other_before  = balanceOf(anybody_else);

    // call transfer
    env e;
    require e.msg.sender == sender;
    bool success = transfer(e, recipient, amount);

    mathint balance_sender_after = balanceOf(sender);
    mathint balance_recip_after   = balanceOf(recipient);
    mathint balance_other_after   = balanceOf(anybody_else);


    if (success) {
        assert balance_recip_after == balance_recip_before + amount,
            "successful transfer(recipient,amount) must increase recipient's balance by amount";

        assert balance_sender_after == balance_sender_before - amount,
            "successful transfer must reduce sender's balance by amount";

        assert balance_other_after == balance_other_before,
            "transfer must not change anybody else's balance";
    } else {
        assert balance_recip_after == balance_recip_before,
            "unsuccessful transfer must not change recipient's balance";

        assert balance_sender_after == balance_sender_before - amount,
            "successful transfer must not change sender's balance";

        assert balance_other_after == balance_other_before,
            "transfer must not change anybody else's balance";
    }
}

definition insufficientBalance(env e, uint amount) returns bool =
    amount > balanceOf(e.msg.sender);

definition transferWouldOverflow(env e, address recipient, uint amount) returns bool =
    (balanceOf(recipient) + amount > max_uint256) && (e.msg.sender != recipient);


rule transferRevertConditions {
    address recipient;
    uint amount;

    env e;
    require e.msg.value == 0; // call to transfer reverts if msg.value > 0

    mathint balance_sender_before = balanceOf(e.msg.sender);
    mathint balance_recip_before  = balanceOf(recipient);
    bool insuffBalance = insufficientBalance(e, amount);
    bool transfWouldOver = transferWouldOverflow(e, recipient, amount);

    transfer@withrevert(e, recipient, amount);

    assert insuffBalance => lastReverted,
        "transfer must revert if sender's balance is insufficient";

    assert transfWouldOver => lastReverted,
        "transfer must revert if recipient's account would overflow";

    assert recipient == 0 => lastReverted,
         "transfer must revert if recipient is 0";

    assert lastReverted 
        => (insuffBalance || transfWouldOver || recipient == 0),
        "transfer must only revert if one of the three revert conditions is true";
//
//     The above only check that transfer _does_ revert as appropriate.  We also
//     want to say that these are the _only_ conditions when transfer reverts.
//     
//     A good option is an "if and only if" expression:

    assert lastReverted <=> (
        insuffBalance
        || transfWouldOver
        || recipient == 0
    ), "transfer must revert if and only if the above conditions are violated";
}

rule onlyOwnerCanDecreaseBalance {
    address owner;

    env e;

    mathint balance_owner_before = balanceOf(owner);
    mathint approved_from_owner_to_caller = allowance(owner, e.msg.sender);

    method f; calldataarg args;
    f(e, args);

    mathint balance_owner_after = balanceOf(owner);

    assert (approved_from_owner_to_caller == 0) && (balance_owner_before > balance_owner_after) 
        => e.msg.sender == owner,
        "only owner can decrease their own balance when didn' approve tokens";

    // Note: this rule is incorrect!  Fixing it is left as an exercise
}

