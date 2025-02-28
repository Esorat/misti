contract C {
    m: map<Address, Int>;
    ms: map<Int, Cell>;
    owner: Address;

    init() {
        self.owner = sender();
    }

    // Entrypoints
    receive(s1: Slice) {
        let a = s1.loadAddress();
        let i = s1.loadInt(64);

        // Bad cases:
        send(SendParameters{ to: a, value: 0, bounce: false, body: emptyCell() }); // Bad
        send(SendParameters{ to: newAddress(0, 0), value: 0, bounce: false, body: s1.asCell() }); // Bad
        self.m.set(a, 42); // Bad
        self.m.del(a); // Bad
        self.ms.del(i+1); // Bad
        self.ms.set(42, s1.asCell()); // Bad

        // Guarded (good) cases:
        if (a != newAddress(0, 0)) { self.m.set(a, 42); } // OK
        self.m.set(myAddress(), 42); // OK - non-tainted address, should be safe
        if (self.checkAddr(a)) { self.m.set(a, 42); } // OK
    }
    
    // Taint propagation examples
    receive(msg: TaintExample) {
        // Simple taint propagation
        let tainted = msg.value;
        self.m.set(msg.addr, tainted); // Bad - unprotected with tainted value
        
        // Taint through parameter
        self.processTainted(msg.addr); // Bad - calls method with tainted value
        
        // Taint with transformation
        let derivedValue = msg.value + 100;
        let derivedAddr = msg.addr;
        send(SendParameters{ to: derivedAddr, value: derivedValue, bounce: false, body: emptyCell() }); // Bad - derived from tainted
        
        // Protected taint example
        if (sender() == self.owner) {
            self.m.set(msg.addr, msg.value); // OK - protected by owner check
            send(SendParameters{ to: msg.addr, value: msg.value, bounce: false, body: emptyCell() }); // OK - protected
        }
        
        // Complex flow with taint and protection
        if (msg.value > 100) {
            let v = msg.value - 100;
            
            if (sender() == self.owner) {
                self.m.set(msg.addr, v); // OK - protected
            } else {
                self.m.set(msg.addr, v); // Bad - derived from tainted and unprotected
            }
        }
    }
    
    // Helper method that uses tainted value
    fun processTainted(a: Address) {
        self.m.set(a, 1000); // Bad - using tainted parameter
    }

    // Utility functions
    fun checkAddr(a: Address): Bool { return a != newAddress(0, 0); }
}

message TaintExample {
    addr: Address;
    value: Int;
}
