module

public section

namespace LeanNDJSONFixture

def Carrier : Type 1 := Type

def useCarrier : Type 1 := Carrier

def identity (A : Type) (a : A) : A := a

def applyCarrier : Type 1 := (fun A : Type 1 => A) Carrier

end LeanNDJSONFixture
