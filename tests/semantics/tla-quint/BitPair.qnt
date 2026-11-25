module BitPair {
  var x: int
  var y: int

  action init = all {
    x' = 0,
    y' = 1,
  }

  action step = {
    nondet flip = Set(false, true).oneOf()
    all {
      x' = y,
      y' = if (flip) 1 - x else x,
    }
  }
}
