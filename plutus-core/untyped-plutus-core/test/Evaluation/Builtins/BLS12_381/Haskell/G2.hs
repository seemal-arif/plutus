{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeApplications  #-}

module Evaluation.Builtins.BLS12_381.Haskell.G2 (tests)
where


import Evaluation.Builtins.BLS12_381.Common
import PlutusCore.BLS12_381.G2 qualified as G2

import Control.Monad (when)
import Data.ByteString as BS (length)
import Data.Either (isLeft)
import Data.List (foldl', genericReplicate)

import Hedgehog
import Hedgehog.Gen qualified as Gen

import Test.Tasty
import Test.Tasty.Hedgehog


---------------- G2 is an Abelian group ----------------

prop_G2_assoc :: TestTree
prop_G2_assoc =
    testPropertyNamed
    "Addition in G2 is associative"
    "G2_assoc" .
    withNTests $ property $ do
      p1 <- forAll genG2element
      p2 <- forAll genG2element
      p3 <- forAll genG2element
      G2.add p1 (G2.add p2 p3) === G2.add (G2.add p1 p2) p3

prop_G2_abelian :: TestTree
prop_G2_abelian =
    testPropertyNamed
    "Addition in G2 is commutative"
    "G2_abelian" .
    withNTests $ property $ do
      p1 <- forAll genG2element
      p2 <- forAll genG2element
      G2.add p1 p2 === G2.add p2 p1

prop_G2_mul :: TestTree
prop_G2_mul =
    testPropertyNamed
    "Scalar multiplication is repeated addition in G2"
    "G2_scalar_multiplication" .
    withNTests $ property $ do
      n <- forAll genSmallScalar
      p <- forAll genG2element
      G2.mul n p === repeatedAddG2 n p
        where repeatedAddG2 :: Integer -> G2.Element -> G2.Element
              repeatedAddG2 n p =
                  if n >= 0
                  then foldl' G2.add G2.zero $ genericReplicate n p
                  else repeatedAddG2 (-n) (G2.neg p)


prop_G2_zero :: TestTree
prop_G2_zero =
    testPropertyNamed
    "The point at infinity is an additive identity in G2"
    "G2_zero" .
    withNTests $ property $ do
      p <- forAll genG2element
      p === G2.add p G2.zero

prop_G2_neg :: TestTree
prop_G2_neg =
    testPropertyNamed
    "Every point in G2 has an additive inverse"
    "G2_inverse" .
    withNTests $ property $ do
      p <- forAll genG2element
      G2.add p (G2.neg p) === G2.zero

test_G2_is_an_Abelian_group :: TestTree
test_G2_is_an_Abelian_group =
    testGroup "G2 is an Abelian group"
         [ prop_G2_assoc
         , prop_G2_zero
         , prop_G2_neg
         , prop_G2_abelian
         ]


---------------- Z acts on G2 correctly ----------------

prop_G2_scalar_inverse :: TestTree
prop_G2_scalar_inverse =
    testPropertyNamed
    "-p = (-1)*p for all p in G2"
    "G2_scalar_inverse" .
    withNTests $ property $ do
      p <- forAll genG2element
      G2.neg p === G2.mul (-1) p

prop_G2_scalar_identity :: TestTree
prop_G2_scalar_identity =
    testPropertyNamed
    "Scalar multiplication by 1 is the identity function on G2"
    "G2_scalar_identity" .
    withNTests $ property $ do
      p <- forAll genG2element
      G2.mul 1 p === p

prop_G2_scalar_zero :: TestTree
prop_G2_scalar_zero =
    testPropertyNamed
    "Scalar multiplication by 0 always yields the zero element of G2"
    "G2_scalar_zero" .
    withNTests $ property $ do
      p <- forAll genG2element
      G2.mul 0 p === G2.zero

prop_G2_scalar_assoc :: TestTree
prop_G2_scalar_assoc =
    testPropertyNamed
    "Scalar multiplication is associative in G2"
    "G2_scalar_assoc" .
    withNTests $ property $ do
      a <- forAll genScalar
      b <- forAll genScalar
      p <- forAll genG2element
      G2.mul (a*b) p === G2.mul a (G2.mul b p)

prop_G2_scalar_distributive :: TestTree
prop_G2_scalar_distributive =
    testPropertyNamed
    "Scalar multiplication distributes over addition in G2"
    "G2_scalar_distributive" .
    withNTests $ property $ do
      a <- forAll genScalar
      b <- forAll genScalar
      p <- forAll genG2element
      G2.mul (a+b) p === G2.add (G2.mul a p) (G2.mul b p)

test_G2_Z_action_good :: TestTree
test_G2_Z_action_good =
    testGroup "Z acts correctly on G2"
         [ prop_G2_scalar_zero
         , prop_G2_scalar_inverse
         , prop_G2_scalar_assoc
         , prop_G2_scalar_distributive
         , prop_G2_scalar_identity
         , prop_G2_mul
         ]


---------------- Compression, uncompression, and hashing work properly ----------------

prop_G2_roundtrip_compression :: TestTree
prop_G2_roundtrip_compression =
    testPropertyNamed
    "Compression followed by uncompression is the identity function on G2"
    "G2_roundtrip_compression" .
    withNTests $ property $ do
      p <- forAll genG2element
      case G2.uncompress (G2.compress p) of
        Left e  -> error $ show e
        Right q -> p === q

-- G2.uncompress should only accept inputs of length 48 (but not all inputs of
-- length 48 are valid)
prop_G2_uncompression_input_size :: TestTree
prop_G2_uncompression_input_size =
    testPropertyNamed
    "G2 uncompression fails if the input has length not equal to 48"
    "G2_uncompression_input_size" .
    withTests 1000 $ property $ do
      b <- forAll $ Gen.filter (\x -> BS.length x /= 48) $ genByteString100
      assert $ isLeft $ G2.uncompress b

prop_G2_hash :: TestTree
prop_G2_hash =
    testPropertyNamed
    "Different inputs hash to different points in G2"
    "G2_no_hash_collisions" .
    withNTests $ property $ do
      b1 <- forAll genByteString
      b2 <- forAll genByteString
      when (b1 /= b2) $  -- Is there a better way to do this?  If some things
                         -- are discarded they're still included in the total
                         -- number of tests (I think).
           G2.hashToCurve b1 /== G2.hashToCurve b2

test_G2_compress_hash :: TestTree
test_G2_compress_hash =
    testGroup "Uncompression and hashing behave properly for G2"
         [ prop_G2_roundtrip_compression
         , prop_G2_uncompression_input_size
         , prop_G2_hash
         ]


-- All the tests

tests :: TestTree
tests =
    testGroup "G2"
        [ test_G2_is_an_Abelian_group
        , test_G2_Z_action_good
        , test_G2_compress_hash
        ]

