package pkg

func foo() {
  //:: ExpectedOutput(type_error)
  assert mset[0..10][0] == 0
}
