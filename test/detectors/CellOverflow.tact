fun refs_num_bad(c: Cell) {
    let b1 = beginCell(); // Bad: 4+ refs
    b1 = b1.storeRef(c);
    b1 = b1.storeRef(c);
    b1 = b1.storeRef(c);
    b1 = b1.storeRef(c);
    b1 = b1.storeRef(c);
    let c1 = b1.endCell();

    let c2 = // Bad: 4+ refs
    beginCell()
        .storeRef(c)
        .storeRef(c)
        .storeRef(c)
        .storeRef(c)
        .storeRef(c)
        .endCell();
}

fun store_size_bad() {
    let b1 = beginCell(); // Bad: 1023+ bits
    b1 = b1.storeInt(42, 257);
    b1 = b1.storeInt(42, 259-2);
    b1 = b1.storeInt(42, 256+1);
    b1 = b1.storeInt(42, 257);
    let c1 = b1.endCell();

    let b2 = beginCell(); // Bad: 1023+ bits
    b2 = b2.storeInt(1, 257)
           .storeInt(1, 257)
           .storeInt(1, 257)
           .storeInt(1, 210); // Total size: 981
    b2 = b2.storeCoins(40000000000); // 44 + 981 = 1025 => overflow
    c1 = b2.endCell();

    let b_1000_bits = beginCell()
           .storeInt(1, 257)
           .storeInt(1, 257)
           .storeInt(1, 257)
           .storeInt(1, 229);
    let b3 = beginCell(); // Bad: 1025 bits
    b3 = b3.storeBuilder(b_1000_bits)
           .storeInt(1, 25);
    c1 = b3.endCell();
}

fun refs_num_ok(c: Cell, copt: Cell?) {
    let c1 = // OK: Cell could be None (no taint analysis yet)
    beginCell()
        .storeRef(c)
        .storeRef(c)
        .storeRef(c)
        .storeMaybeRef(copt)
        .storeRef(c)
        .endCell();

    // OK: no assignments to the result of storeRef calls
    let b1 = beginCell(); // Bad: 4+ refs
    b1.storeRef(c);
    b1.storeRef(c);
    b1.storeRef(c);
    b1.storeRef(c);
    b1.storeRef(c);
    c1 = b1.endCell();
}

