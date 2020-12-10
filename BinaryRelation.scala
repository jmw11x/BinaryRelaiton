object BinaryRelation {
  type BinaryRelation = (Int, Int) => Boolean
  type Element = (Int, Int)
  val bound = 99

  // returns an empty binary relation, i.e. no pairs
  def emptyBinaryRelation: BinaryRelation = (x, y) => false

  // returns the universal binary relation, i.e. all pairs
  def universalBinaryRelation: BinaryRelation = (x, y) => true

  // returns true of e is in r, false otherwise
  def contains(r: BinaryRelation, e: Element): Boolean = r(e._1, e._2)

  // returns true if r1 is a subset of r2, false otherwise
  def subRelation(r1: BinaryRelation, r2: BinaryRelation): Boolean = {
    def helper1(x: Int): Boolean = {
      def helper2(y: Int): Boolean = {
        if (y > bound) true
        else if (contains(r1, (x, y)) && !contains(r2, (x, y))) false
        else helper2(y + 1)
      }
      if (x > bound) true
      else if (!helper2(0)) false
      else helper1(x + 1)
    }
    helper1(0)
  }

  // returns true of r1 equals r2, false otherwise
  def equal(r1: BinaryRelation, r2: BinaryRelation): Boolean = {
    val list = for {
        i <- 0 to bound
        j <- 0 to bound
        if contains(r1, (i, j))
      }yield((r1(i, j) == r2(i, j)))
      !((list filter(x => x == true)).toList.isEmpty)
  }

  // returns a new binary relation obtained by adding e to r
  def add(r: BinaryRelation, e: Element): BinaryRelation = {
    (x, y) => if((x == e._1) && (y == e._2)) true else r(x, y)
  }

  // for all a, (a,a) is in r
  def reflexive(r: BinaryRelation): Boolean = {
    def helper1(x: Int): Boolean = {
        def helper2(y: Int): Boolean = if(!r(x, y)) false else true
        if (x > bound) true
        else if(!helper2(x)) false
        else helper1(x + 1)
    }
    helper1(0)
  }

  // for all a,b, if (a,b) is in r then (b,a) is also in r
  def symmetric(r: BinaryRelation): Boolean = {
      val list = for {
          i <- 0 to bound
          j <- 0 to bound
          if(contains(r, (i, j)) && contains(r, (j, i)))
      }yield((j, i))
      list.toList.length > 0
  }

  // for all a,b,c, if (a,b) is in r and (b,c) is in r then (a,c) is also in r
  def transitive(r: BinaryRelation): Boolean = {
      val list = for {
          i <- 0 to bound
          j <- 0 to bound
          k <- 0 to bound
          if contains(r, (j, k)) && contains(r, (i, j)) && i != k
      }yield ((i, k))
      list.toList.length > 0
  }

  // For all a,b, if a != b and (a,b) in r then (b,a) is not in r
  def antisymmetric(r: BinaryRelation): Boolean = {
      val list = for {
        i <- 0 to bound
        j <- 0 to bound
        if(contains(r, (i, j)) && i != j && contains(r, (j, i)))
      }yield((i,j))
      list.toList.length == 0
  }

  // returns set union of r1 and r2
  def union(r1: BinaryRelation, r2: BinaryRelation): BinaryRelation = {
    val U = for {
        i <- 0 to bound
        j <- 0 to bound
        if(contains(r1, (i, j)) || contains(r2, (i, j)))
    }yield((i,j))
    (U foldLeft emptyBinaryRelation)((x, y) => add(x, y))
  }

  // returns inverse of r; inverse(r) = { (b,a) | (a,b) in r }
  def inverse(r: BinaryRelation): BinaryRelation = {
      val U = for {
        i <- 0 to bound
        j <- 0 to bound
        if(contains(r,(i, j)))
    }yield((j, i))
    (U foldLeft emptyBinaryRelation)((x, y) => add(x, y))
  }

  // all (a,a) in A
  def reflexiveClosure(r: BinaryRelation): BinaryRelation =
    union(r,(((0 to bound) zip (0 to bound)).toList foldLeft emptyBinaryRelation) ((x,y) => add(x,y)))

  // for all a,b, if (a,b) is in r then (b,a) is also in r
  def symmetricClosure(r: BinaryRelation): BinaryRelation = {
      val pairs = for {
        i <- 0 to bound
        j <- 0 to bound
        if(contains(r, (i, j)))
    }yield((j, i))
    (pairs foldLeft r)((x, y) => add(x, y))
  }

  // returns a new relation { (a,c) | (a,b) is in r and (b,c) is in r for all a,b,c in Z in the set {bound x bound}
  def selfJoin(r: BinaryRelation): BinaryRelation = {
    val list = for {
          i <- 0 to bound
          j <- 0 to bound
          k <- 0 to bound
          if contains(r, (j,k)) && contains(r, (i,j))
      }yield ((i,k))
      (list foldLeft r) ((x,y) => add(x, y))
  }

  // if((x,y) && (y,z) in R) ->(x,z) needs to be added
  def transitiveClosure(r: BinaryRelation): BinaryRelation = selfJoin(r)

  def toString(r: BinaryRelation): String = {
    val rs = for {
      i <- 0 to bound
      j <- 0 to bound
      if contains(r, (i, j))
    } yield ((i,j))
    rs.mkString("{", ",", "}")
  }

  def printBinaryRelation(r: BinaryRelation): Unit = {
    println(toString(r))
  }
}
