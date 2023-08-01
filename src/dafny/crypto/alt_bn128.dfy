/*
 * Copyright 2022 ConsenSys Software Inc.
 *
 * Licensed under the Apache License, Version 2.0 (the "License"); you may
 * not use this file except in compliance with the License. You may obtain
 * a copy of the License at http://www.apache.org/licenses/LICENSE-2.0
     *
 * Unless required by applicable law or agreed to in writing, software dis-
 * tributed under the License is distributed on an "AS IS" BASIS, WITHOUT
 * WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied. See the
 * License for the specific language governing permissions and limitations
 * under the License.
 */
include "../util/int.dfy"

module FiniteField {
    import opened Int

    type pos = n:nat | n > 0 witness 1

    // The number of elements in the given field.
    const N : pos

    // Define the raw set of field elements.
    type Field = n:nat | n < N

    // Add two elements from the field together.
    function Add(lhs: Field, rhs: Field) : Field {
        (lhs+rhs) % N
    }

    // Subtract one element from another.
    function Sub(lhs: Field, rhs: Field) : Field {
        (lhs-rhs) % N
    }

    // Multiply two elements together.
    function Mul(lhs: Field, rhs: Field) : Field {
        (lhs*rhs) % N
    }

    // Divide one element into another.
    function Div(lhs: Field, rhs: Field) : Field
    requires IsPrime(N) {
        if rhs == 0 then 0
        else
            assert rhs < N;
            Int.PrimeFieldsHaveInverse(rhs,N);
            var inverse := Int.Inverse(rhs,N).Unwrap();
            (lhs * inverse) % N
    }

    // Raise field element to a given power.
    function Pow(lhs: Field, n: nat) : Field {
        Int.ModPow(lhs,n,N)
    }
}

// An elliptic curve wheter y^2 == x^3 + Ax + B
module EllipticCurve refines FiniteField {
    import opened Optional
    // Define the so-called "point at infinity"
    const INFINITY : (nat,nat) := (0,0)
    // Parameter defining the curve
    const A : Field
    // Paramter defining the curve
    const B : Field
    /// Equation defining this particular elliptic curve.
    function Curve(x:Field,y:Field) : bool {
        // NOTE: should be field operations?
        Pow(y,2) == (Pow(x,3) + Mul(A,x) + B) % N
    }
    // A point on the curve is either INFINITY or a valid point on the curve.
    type Point = p:(Field,Field) | p == INFINITY || Curve(p.0,p.1) witness INFINITY

    // Add two points on the curve together producing another point on the curve.
    function PointAdd(p: Point, q: Point) : (r:Point)
    requires N > 3 && IsPrime(N)
    {
        var x_p := p.0;
        var x_q := q.0;
        var y_p := p.1;
        var y_q := q.1;
        //
        if p == INFINITY then q
        else if q == INFINITY then p
        else if p == q then Double(p)
        else
            var x_diff := Sub(x_q,x_p);
            if x_diff == 0 then INFINITY
            else
                var y_diff := Sub(y_q,y_p);
                var lam := Div(y_diff,x_diff);
                var x_r := Sub(Sub(Pow(lam,2),x_p),x_q);
                var y_r := Sub(Mul(lam,Sub(x_p,x_r)),y_p);
                // FIXME: Dafny cannot prove this?
                if Curve(x_r,y_r)
                then
                    (x_r,y_r)
                else
                    INFINITY
    }

    function Double(p:Point) : (r:Point)
    requires N > 3 && IsPrime(N)
    requires p != INFINITY {
        var x := p.0;
        var y := p.1;
        var top := Add(Mul(3,Pow(x,2)),A);
        var bottom := Mul(2,y);
        // Is this guaranteed not to hold?
        if bottom == 0 then INFINITY
        else
            var lam := Div(top,bottom);
            var x_r := Sub(Sub(Pow(lam,2),x),x);
            var y_r := Sub(Mul(lam,Sub(x,x_r)),y);
            // FIXME: Dafny cannot prove this?
            if Curve(x_r,y_r)
            then
                var rp : Point := (x_r,y_r);
                rp
            else
                INFINITY
    }

    // Multiply a point by a given factor on the curve.
    function PointMul(p: Point, n: u256) : (r:Point)
    requires N > 3 && IsPrime(N)
    decreases n
    {
        if n == 0 then INFINITY
        else
            var res := PointMul(PointAdd(p,p),n / 2);
            if n % 2 == 1 then PointAdd(res,p)
            else res
    }
}

// The ellptic curve given by y^2 == x^3 + 3.
module AltBn128 refines EllipticCurve {
    // Specify the number of elements in the finite field
    const N := ALT_BN128_PRIME
    // As per EIP196
    const ALT_BN128_PRIME := 21888242871839275222246405745257275088696311157297823662689037894645226208583
    // Parameters for the curve
    const A := 0
    const B := 3

    // Axiom to establish that this is really a prime field.  This is needed
    // because Dafny cannot possible determine that ALT_BN128_PRIME is a prime.
    lemma {:axiom} IsPrimeField()
    ensures IsPrime(ALT_BN128_PRIME) {
        assume {:axiom} IsPrime(ALT_BN128_PRIME);
    }

    // Attempt to construct an element of the prime field.  This will only
    // succeed if it is indeed a member, otherwise it returns nothing.
    function BNF(val:nat) : (r:Option<Field>)
    {
        // Check whether it is a member of the field
        if val < ALT_BN128_PRIME then
            Some(val)
        else
            None
    }

    // Construct a point on the BN128 curve.  This will only succeed if it is
    // indeed on the curve, otherwise it returns nothing.
    function BNP(x: Field, y: Field) : Option<Point> {
        // Check whether or not the point is actually on the curve.
        if (x,y) == INFINITY || Curve(x,y)
        then
            var bnp : Point := (x,y);
            Some(bnp)
        else
            None
    }
}
