module Ex91fromTDDIsamplesWithMods

import Decidable.Equality

-- Ex. 2, pp. 249f:

data Last : List a -> a -> Type where
     LastOne : Last [value] value
     LastCons : (prf : Last xs value) -> Last (x :: xs) value


lastNotNil : (value : a) -> Last [] x -> Void
lastNotNil _ LastOne impossible
lastNotNil _ (LastCons _) impossible


lastNotSingleton : (contra : (y = value) -> Void) -> Last [y] value -> Void
lastNotSingleton contra LastOne = contra Refl
lastNotSingleton _ (LastCons LastOne) impossible
lastNotSingleton _ (LastCons (LastCons _)) impossible


lastNotCons : (contra: Last xs value -> Void) -> Last (x :: xs) value -> Void
lastNotCons contra LastOne = ?lastNotCons_rhs_0
lastNotCons contra (LastCons prf) = contra prf


isLast : DecEq a => (xs : List a) -> (value : a) -> Dec (Last xs value)
isLast [] value = No (lastNotNil value)
isLast [y] value = case decEq y value of
                        (Yes Refl) => Yes LastOne
                        (No contra) => No (lastNotSingleton contra)
isLast (x :: xs) value = case isLast xs value of
                              (Yes prf) => Yes (LastCons prf)
                              (No contra) => No (lastNotCons contra)
