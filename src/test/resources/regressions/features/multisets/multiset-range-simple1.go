package pkg

func example1() {
  ghost s := mset[1..10]
  assert s == mset ( seq [ 1 .. 10 ] )
}

func example2() {
  assert mset[1 .. 1] == mset[int] { }
  
  // could we do without the first assertion?
  assert seq[1 .. 2] == seq[int] { 1 } 
  assert mset[1 .. 2] == mset[int] { 1 }
  
  // could we do without the first assertion?
  assert seq[1..10] == seq[int] { 1, 2, 3, 4, 5, 6, 7, 8, 9 } 
  assert 0 < 3 in mset[1 .. 10]
  assert 0 < 2 + 3 in mset[1 .. 10]
  assert 42 in mset[1 .. 10] == 0
}

func example3() {
  assert seq[1 .. 4] == seq[int] { 1, 2, 3 }
  assert seq[4 .. 7] == seq[int] { 4, 5, 6 }
  assert seq[1 .. 7] == seq[1 .. 4] ++ seq[4 .. 7]
  
  assert mset[1 .. 4] union mset[4 .. 7] == mset[1 .. 7]
}

func example4() {
  assert |mset[1 .. 4]| == 3
}

func example5() {
  assert mset[4 .. 1] == mset[int] { }
}
