{-# LANGUAGE GADTs #-}

module Test where


data  Foo a where
  F ::  b -> Foo b
  G :: Int -> Foo Int



instance Show a => Show (Foo a) where
  show (F b) = show b
  show (G i) = show i 

