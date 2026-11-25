module BoundedCounter {
  var n: int

  action init = n' = 0

  action step = all {
    n < 2,
    n' = n + 1,
  }
}
