{-# LANGUAGE StandaloneDeriving, FlexibleInstances #-}
import qualified VsSahlq_instant20
import qualified Modal
import qualified Datatypes
import qualified SecOrder

{- coq naturals to haskell Ints -}
c2hn :: Datatypes.Coq_nat -> Int
c2hn Datatypes.O = 0
c2hn (Datatypes.S n) = (c2hn n) + 1

{- Haskell Ints to Coq naturals -}
h2cn :: Int -> Datatypes.Coq_nat
h2cn 0 = Datatypes.O
h2cn n = Datatypes.S (h2cn (n-1))

-- propositional variables
p :: Int -> Modal.Modal
p n = Modal.Coq_atom (h2cn n)

-- conjunction
(/\) :: Modal.Modal -> Modal.Modal -> Modal.Modal
(/\) phi psi = Modal.Coq_mconj phi psi

-- disjunction
(\/) :: Modal.Modal -> Modal.Modal -> Modal.Modal
(\/) phi psi = Modal.Coq_mdisj phi psi

-- negation

neg :: Modal.Modal -> Modal.Modal
neg phi = Modal.Coq_mneg phi

-- implication
(-->) :: Modal.Modal -> Modal.Modal -> Modal.Modal
(-->) phi psi = Modal.Coq_mimpl phi psi

-- box
box :: Modal.Modal -> Modal.Modal
box phi = Modal.Coq_box phi

-- diamond
dia :: Modal.Modal -> Modal.Modal
dia phi = Modal.Coq_diam phi

instance Show SecOrder.SecOrder where
  show (SecOrder.Coq_predSO n m) = "[what is this?]"
  show (SecOrder.Coq_relatSO n m) = "R(x" ++ (show (c2hn n)) ++ ", x" ++ (show (c2hn m)) ++ ")"
  show (SecOrder.Coq_eqFO n m) = "(x" ++ (show (c2hn n)) ++ " = x" ++ (show (c2hn m)) ++ ")"
  show (SecOrder.Coq_allFO n phi) = "(all x" ++ (show $ c2hn n) ++ "." ++ (show phi) ++ ")"
  show (SecOrder.Coq_exFO n phi) = "(ex x" ++ (show $ c2hn n) ++ "." ++ (show phi) ++ ")"
  show (SecOrder.Coq_negSO phi) = "(not " ++ (show phi) ++ ")"
  show (SecOrder.Coq_conjSO phi psi) = "(" ++ (show phi) ++ "/\\" ++ (show psi) ++ ")"
  show (SecOrder.Coq_disjSO phi psi) = "(" ++ (show phi) ++ "\\/" ++ (show psi) ++ ")"
  show (SecOrder.Coq_implSO phi psi) = "(" ++ (show phi) ++ "-->" ++ (show psi) ++ ")"
  show (SecOrder.Coq_allSO _ _) = "[shouldn't happen!]"
  show (SecOrder.Coq_exSO _ _) = "[shouldn't happen!]"

corr :: Modal.Modal -> SecOrder.SecOrder
corr phi = VsSahlq_instant20.vsSahlq_full_Modal phi
