{-# LANGUAGE TypeOperators #-}

data a :/\: b = a :/\: b
data a :\/: b = L a | R b

data False
type Not a = a -> False

data a :<->: b = Bi {
  forward  :: (a -> b),
  backward :: (b -> a)
}

lhs :: a :/\: b -> a
rhs :: a :/\: b -> b

lhs (p :/\: _) = p
rhs (_ :/\: q) = q

and_commute :: a :/\: b -> b :/\: a
and_commute (p :/\: q) = (q :/\: p)

or_commute :: a :\/: b -> b :\/: a
or_commute (L a) = R a
or_commute (R a) = L a

and_assoc :: a :/\: (b :/\: c) -> (a :/\: b) :/\: c
and_assoc (a :/\: (b :/\: c)) = (a :/\: b) :/\: c

or_assoc :: a :\/: (b :\/: c) -> (a :\/: b) :\/: c
or_assoc (R (R c)) = R c
or_assoc (R (L b)) = L (R b)
or_assoc (L a)     = L (L a)

modus_ponens :: a -> (a -> b) -> b
modus_ponens a f = f a

and_idempotent :: a :/\: a -> a
and_idempotent (a :/\: _) = a

or_idempotent :: a :\/: a -> a
or_idempotent (L a) = a
or_idempotent (R a) = a

and_distributes :: a :/\: (b :\/: c) -> (a :/\: b) :\/: (a :/\: c)
and_distributes (a :/\: (L b)) = L (a :/\: b)
and_distributes (a :/\: (R c)) = R (a :/\: c)

or_distributes :: a :\/: (b :/\: c) -> (a :\/: b) :/\: (a :\/: c)
or_distributes (L a)          = (L a) :/\: (L a)
or_distributes (R (b :/\: c)) = (R b) :/\: (R c)

contrapositive :: (a -> b) -> Not b -> Not a
contrapositive f g = g . f

-- demorgan1 :: (a -> False) :\/: (b -> False) -> (a :/\: b) -> False
-- andys:
-- demorgan1 (L f) (a :/\: b) = f a
-- demorgan1 (R g) (a :/\: b) = g b
demorgan1 :: Not a :\/: Not b -> Not (a :/\: b)
-- noons:
demorgan1 (L f) = f . lhs
demorgan1 (R g) = g . rhs


demorgan2a :: Not a :/\: Not b -> Not (a :\/: b)
demorgan2a (f :/\: _) (L a) = f a
demorgan2a (_ :/\: g) (R b) = g b

demorgan2b :: Not (a :\/: b) -> Not a :/\: Not b
-- demorgan2b :: ((a :\/: b) -> False) -> (a -> False) :/\: (b -> False)
demorgan2b f = (f . L) :/\: (f . R)

demorgan2 :: Not a :/\: Not b :<->: Not (a :\/: b)
-- demorgan2 :: (a -> False) :/\: (b -> False) :<->: ((a :\/: b) -> False)
demorgan2 = Bi { forward = demorgan2a, backward = demorgan2b }

data Scottish    = Scottish
data RedSocks    = RedSocks
data WearKilt    = WearKilt
data Married     = Married
data GoOutSunday = GoOutSunday

no_true_scottsman ::
  (Not Scottish -> RedSocks)          -> -- rule 1
  (WearKilt :\/: Not RedSocks)        -> -- rule 2
  (Married -> Not GoOutSunday)        -> -- rule 3
  (Scottish :<->: GoOutSunday)        -> -- rule 4
  (WearKilt -> Scottish :/\: Married) -> -- rule 5
  (Scottish -> WearKilt)              -> -- rule 6
  False

no_true_scottsman
  rule1
  rule2
  rule3
  rule4
  rule5
  rule6 = let
    lemma1 :: Scottish -> Married
    lemma1 = rhs . rule5 . rule6

    lemma2 :: Scottish -> Not GoOutSunday
    -- lemma2 = rule3 . lemma1
    -- Noons:
    lemma2 = const $ contrapositive (backward rule4) lemma4

    lemma3 :: Scottish -> GoOutSunday
    lemma3 = forward rule4

    lemma4 :: Not Scottish
    lemma4 scottish = modus_ponens (lemma3 scottish) (lemma2 scottish)

    lemma5 :: RedSocks
    lemma5 = rule1 lemma4

    lemma6 :: WearKilt :\/: False
    lemma6 = case rule2 of
                    L w -> L w
                    R f -> R (f lemma5)

    lemma7 :: Not WearKilt -> False
    lemma7 = case lemma6 of
                    L k -> modus_ponens k
                    R f -> const f

    -- lemma8 :: (Scottish -> False) -> (WearKilt -> False)
    -- lemma8 :: (Scottish -> False) -> WearKilt -> False
    lemma8 :: Not Scottish -> Not WearKilt
    -- lemma8 f kilt = modus_ponens (lhs (rule5 kilt)) f
    lemma8 f kilt = f (lhs (rule5 kilt))

    lemma9 :: Not Scottish -> False
    lemma9 = lemma7 . lemma8

    in lemma9 lemma4


