struct A {
    x: Int;
    m: map<Int, Int>;
}

trait T {
  balance: Int;
  m: map<Int, Int>;
  a: A;
}

contract C with T {
  balance: Int = 42;
  m: map<Int, Int>;
  a: A;

  init(m: map<Int, Int>, a: A) {
    // OK: cannot access self to call a setter method
    self.m = m;
    self.a = a;
  }

  fun updateBalance() {
    // Bad cases
    self.balance = 100;
    self.balance -= 100;
    self.m.set(3, 3);
    self.m.del(3);
    self.a.x = 42;
    self.a.x += 42;
    self.a.m.set(3, 3);
    self.a.m.del(3);
  }
}

trait Z {
  balance: Int;
  fun setBalance(newBalance: Int) {
    require(newBalance > 0, "balance cannot be negative"); // Invariant check
    self.balance = newBalance;
  }
}

contract V with Z {
  balance: Int = 42;
  fun updateBalance() {
    self.setBalance(100); // OK: Invariant preserved
  }
}
