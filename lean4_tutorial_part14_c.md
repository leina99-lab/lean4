# Part 14-C: 논리 게이트와 회로 설계 — 인버터, OR/AND 게이트, 가산기

> **Rosen 이산수학 8판 · Section 12.3 기반**
> **『Mathematics in Lean』 + Lean 4 공식화**

---

## 0. 들어가며: 이 파트에서 배울 것

Part 14-A, 14-B에서는 부울 대수의 **수학적 법칙**을 배웠다. 이번 Part 14-C에서는 그 법칙들이 실제로 어떻게 **물리적 회로**로 구현되는지 배운다. 부울 함수 → 논리 게이트 → 디지털 회로로 이어지는 과정을 Lean 4로 모델링한다.

이 파트에서 다루는 내용:

1. **논리 게이트**(logic gate)의 세 가지 기본 형태: 인버터, OR 게이트, AND 게이트
2. 게이트를 **조합**하여 회로 만들기
3. **실용 회로 예제**: 3인 투표기, 조명 제어 회로
4. **가산기**(adder): 반가산기와 전가산기 — 컴퓨터 덧셈의 핵심
5. Lean 4로 회로를 **함수로 모델링**하고 정확성을 **검증**하기

> 💡 **핵심 메시지**: 논리 게이트는 부울 연산의 물리적 구현이다. 수학적으로 올바른 부울 식이 있으면, 그것을 기계적으로 회로로 바꿀 수 있다!

---

## 1. 논리 게이트란? — 부울 연산의 물리적 구현

**게이트**(gate)란 0과 1의 입력을 받아 부울 연산을 수행하고 0 또는 1을 출력하는 기본 장치이다. 디지털 회로의 **가장 작은 빌딩 블록**이다.

> 🧱 **비유**: 부울 연산이 "레시피"라면, 게이트는 그 레시피를 실행하는 "주방 도구"이다.

### 1.1 인버터 (Inverter) — NOT 게이트

**입력 1개, 출력 1개**. 입력의 보수를 출력한다.

```
입력 x ──▷○── 출력 x̄
```

| 입력 $x$ | 출력 $\overline{x}$ |
|---------|-------------------|
| 0       | 1                 |
| 1       | 0                 |

```lean
-- 인버터를 Lean 4 함수로
def inverter (x : Bool) : Bool := !x

#eval inverter true   -- false
#eval inverter false  -- true
```

### 1.2 OR 게이트 — 부울 합

**입력 2개 이상, 출력 1개**. 입력들의 부울 합을 출력한다.

```
입력 x ──┐
         ├─D── 출력 x + y
입력 y ──┘
```

| $x$ | $y$ | 출력 $x + y$ |
|-----|-----|-------------|
| 0   | 0   | 0           |
| 0   | 1   | 1           |
| 1   | 0   | 1           |
| 1   | 1   | 1           |

```lean
def orGate (x y : Bool) : Bool := x || y

-- n개 입력 OR 게이트
def orGateN (inputs : List Bool) : Bool := inputs.any id
```

### 1.3 AND 게이트 — 부울 곱

**입력 2개 이상, 출력 1개**. 입력들의 부울 곱을 출력한다.

```
입력 x ──┐
         ├─D── 출력 x · y
입력 y ──┘
```

| $x$ | $y$ | 출력 $x \cdot y$ |
|-----|-----|-----------------|
| 0   | 0   | 0               |
| 0   | 1   | 0               |
| 1   | 0   | 0               |
| 1   | 1   | 1               |

```lean
def andGate (x y : Bool) : Bool := x && y

-- n개 입력 AND 게이트
def andGateN (inputs : List Bool) : Bool := inputs.all id
```

### 1.4 세 게이트의 대응 정리

| 게이트 | 부울 연산 | 논리 연산 | Lean 4 |
|--------|---------|---------|--------|
| **인버터**(Inverter) | $\overline{x}$ | $\lnot x$ | `!x` |
| **OR 게이트** | $x + y$ | $x \lor y$ | `x \|\| y` |
| **AND 게이트** | $x \cdot y$ | $x \land y$ | `x && y` |

> 💡 이 세 가지 게이트만 있으면 **모든** 부울 함수를 회로로 구현할 수 있다. 왜냐하면 Part 14-B에서 배운 것처럼 $\{+, \cdot, \overline{\phantom{x}}\}$가 **함수적으로 완전**하기 때문이다!

---

## 2. 조합 회로 — 게이트를 연결하여 복잡한 기능 만들기

### 2.1 조합 회로란?

**조합 회로**(combinational circuit)는 인버터, OR 게이트, AND 게이트를 조합하여 만든 회로이다. 특징:
- 데이터 **기억 능력이 없다** (입력만으로 출력이 결정된다)
- 입력에 따라 설계된 대로 출력을 내놓는다

참고로 데이터를 기억할 수 있는 회로는 **순차 회로**(sequential circuit)라고 한다 (플립플롭 등).

### 2.2 회로의 Lean 4 모델링

Lean 4에서 조합 회로는 그냥 **함수**이다! 입력을 받아 출력을 내는 함수.

**예제 1** (Rosen): 다음 출력을 갖는 회로를 구성하라.

**(a)** $\overline{x}(x + y)$

```lean
-- 회로 함수
def circuit_a (x y : Bool) : Bool := (!x) && (x || y)

-- 이것은 사실 더 간단하게 쓸 수 있다!
-- x̄(x + y) = x̄·x + x̄·y = 0 + x̄y = x̄y
-- 분배 법칙으로 전개하면 x̄y와 같다

-- 동치 확인
example : ∀ x y : Bool, (!x) && (x || y) = (!x) && y := by decide
```

> 이처럼 회로를 먼저 부울 식으로 쓰고, 부울 법칙으로 **간소화**한 뒤 구현하면 게이트 수를 줄일 수 있다!

**(b)** $x(y + z)$

```lean
def circuit_b (x y z : Bool) : Bool := x && (y || z)
```

**(c)** $(x + y + \overline{z}) \cdot x\overline{y}z \cdot \overline{x}yz$

```lean
def circuit_c (x y z : Bool) : Bool :=
  (x || y || !z) && (x && !y && z) && (!x && y && z)

-- 이 회로의 출력을 모든 경우에 대해 확인
#eval circuit_c true true true    -- false
#eval circuit_c false true true   -- false
-- 실제로 이 함수는 항상 false를 출력한다!
example : ∀ x y z : Bool, circuit_c x y z = false := by decide
```

---

## 3. 실용 회로 예제 (1): 3인 다수결 투표기

### 3.1 문제 (Rosen 예제 2)

3인으로 구성된 위원회에서 다수결 투표를 한다. 2인 이상이 '예'를 하면 안건이 통과된다. 이것을 결정하는 회로를 설계하라.

### 3.2 분석

변수 정의:
- $x$: 첫 번째 사람 ('예'=1, '아니오'=0)
- $y$: 두 번째 사람
- $z$: 세 번째 사람
- 출력: 2명 이상이 1이면 1

진리표:

| $x$ | $y$ | $z$ | 출력 | 이유 |
|-----|-----|-----|------|------|
| 1   | 1   | 1   | **1** | 3명 찬성 |
| 1   | 1   | 0   | **1** | 2명 찬성 |
| 1   | 0   | 1   | **1** | 2명 찬성 |
| 1   | 0   | 0   | 0 | 1명 찬성 |
| 0   | 1   | 1   | **1** | 2명 찬성 |
| 0   | 1   | 0   | 0 | 1명 찬성 |
| 0   | 0   | 1   | 0 | 1명 찬성 |
| 0   | 0   | 0   | 0 | 0명 찬성 |

부울 식: $F = xy + xz + yz$

이것은 "3개 중 2개 이상이 1" ↔ "최소한 하나의 쌍이 모두 1"이라는 의미이다.

### 3.3 Lean 4 구현 및 검증

```lean
-- 다수결 투표기 회로
def majorityVote (x y z : Bool) : Bool := (x && y) || (x && z) || (y && z)

-- "2명 이상 찬성"이라는 사양(specification)을 별도로 정의
def atLeastTwo (x y z : Bool) : Bool :=
  -- x, y, z를 Nat으로 변환하여 합이 2 이상인지 확인
  let count := (if x then 1 else 0) + (if y then 1 else 0) + (if z then 1 else 0)
  count >= 2

-- 회로가 사양을 만족함을 증명!
example : ∀ x y z : Bool, majorityVote x y z = atLeastTwo x y z := by decide
```

> 🎯 **핵심**: 회로 함수(`majorityVote`)와 사양 함수(`atLeastTwo`)를 **별도로** 정의한 뒤, 둘이 동치임을 **증명**한다. 이것이 **형식 검증**(formal verification)의 핵심 아이디어이다!

### 3.4 5인 다수결 투표기 (연습문제 7)

5인 위원회로 확장해 보자:

```lean
def majorityVote5 (a b c d e : Bool) : Bool :=
  -- 곱의 합 표준형으로 쓰면 매우 길어진다.
  -- 대신 "3명 이상 찬성"으로 정의하자
  let count := (if a then 1 else 0) + (if b then 1 else 0) +
               (if c then 1 else 0) + (if d then 1 else 0) +
               (if e then 1 else 0)
  count >= 3

-- 또는 부울 식으로: 10개의 3인 조합의 OR
def majorityVote5_gates (a b c d e : Bool) : Bool :=
  (a && b && c) || (a && b && d) || (a && b && e) ||
  (a && c && d) || (a && c && e) || (a && d && e) ||
  (b && c && d) || (b && c && e) || (b && d && e) ||
  (c && d && e)

example : ∀ a b c d e : Bool,
  majorityVote5 a b c d e = majorityVote5_gates a b c d e := by decide
```

---

## 4. 실용 회로 예제 (2): 조명 제어 회로

### 4.1 2-스위치 조명 제어 (Rosen 예제 3)

2개의 스위치가 있고, 어느 하나를 누르면 조명등의 상태가 반전된다.

초기 상태: 두 스위치 모두 닫힘(1), 조명 켜짐(1)

| $x$ | $y$ | 조명 $F(x,y)$ |
|-----|-----|-------------|
| 1   | 1   | **1** (초기) |
| 1   | 0   | 0 (y 바꿈) |
| 0   | 1   | 0 (x 바꿈) |
| 0   | 0   | **1** (둘 다 바꿈) |

이것은 사실 **XNOR** (배타적 NOR, XOR의 부정)이다!

$$F(x, y) = xy + \overline{x}\overline{y} = \overline{x \oplus y}$$

```lean
def lightSwitch2 (x y : Bool) : Bool := (x && y) || (!x && !y)

-- 이것은 XNOR과 같다
example : ∀ x y : Bool, lightSwitch2 x y = !(xor x y) := by decide

-- 사양: "두 스위치가 같은 상태이면 켜짐"
example : ∀ x y : Bool, lightSwitch2 x y = (x == y) := by decide
```

### 4.2 3-스위치 조명 제어

3개의 스위치 중 어느 하나를 바꾸면 조명 상태가 반전된다. 초기 상태: 모두 닫힘, 조명 켜짐.

| $x$ | $y$ | $z$ | 조명 |
|-----|-----|-----|------|
| 1   | 1   | 1   | **1** |
| 1   | 1   | 0   | 0 |
| 1   | 0   | 1   | 0 |
| 1   | 0   | 0   | **1** |
| 0   | 1   | 1   | 0 |
| 0   | 1   | 0   | **1** |
| 0   | 0   | 1   | **1** |
| 0   | 0   | 0   | 0 |

패턴: 1의 개수가 **홀수**이면 0, **짝수**(0 포함)이면... 아니다, 표를 다시 보면 1의 개수가 홀수(1개 또는 3개)인 경우는 1이 되는 게 $(1,1,1), (1,0,0), (0,1,0), (0,0,1)$ — 즉 홀수 개가 1이면 조명이 켜진다!

$$F = xyz + x\overline{y}\overline{z} + \overline{x}y\overline{z} + \overline{x}\overline{y}z$$

이것은 사실 $x \oplus y \oplus z$의 **부정**이다. 아니, 다시 확인하면:

실제로 $F(1,1,1) = 1$이고 1이 3개(홀수)이므로... 이것은 1의 개수가 홀수이면 1이 아니라, "바뀐 스위치 수가 짝수이면 1"이다. 초기가 (1,1,1)에서 시작하므로, (1,1,1)과의 해밍 거리가 짝수이면 조명이 켜진다.

정리하면 이 함수는 **3-입력 XNOR**: $F = \overline{x \oplus y \oplus z}$... 가 아니라, 표를 다시 보면:

$F = xyz + x\overline{y}\overline{z} + \overline{x}y\overline{z} + \overline{x}\overline{y}z$

```lean
def lightSwitch3 (x y z : Bool) : Bool :=
  (x && y && z) || (x && !y && !z) || (!x && y && !z) || (!x && !y && z)

-- 확인: 이것은 XOR의 NOT이 아니라, XOR 자체도 아니다.
-- 사실 이것은 "1의 개수가 홀수"인지와 관련이 있다.
-- 검증:
#eval lightSwitch3 true true true    -- true  (3개 = 홀수)
#eval lightSwitch3 true false false  -- true  (1개 = 홀수)
#eval lightSwitch3 false true false  -- true  (1개 = 홀수)
#eval lightSwitch3 false false true  -- true  (1개 = 홀수)
#eval lightSwitch3 true true false   -- false (2개 = 짝수)

-- 맞다! "1의 개수가 홀수이면 1" = XOR
-- 즉 이것은 x XOR y XOR z 와 같다!
example : ∀ x y z : Bool,
  lightSwitch3 x y z = xor (xor x y) z := by decide
```

---

## 5. 가산기 — 컴퓨터 덧셈의 핵심 ⭐

### 5.1 반가산기 (Half Adder)

**반가산기**(half adder)는 1비트 두 개를 더하여 **합**(sum)과 **올림수**(carry)를 출력하는 회로이다.

> 🧮 **비유**: 한 자릿수 덧셈에서 "결과 자릿수"와 "올림(받아올림)"을 구하는 것이다. 예를 들어 $1 + 1 = 10_2$에서 합이 0이고 올림수가 1이다.

| 입력 $x$ | 입력 $y$ | 합 $s$ | 올림수 $c$ |
|---------|---------|--------|----------|
| 0       | 0       | 0      | 0        |
| 0       | 1       | 1      | 0        |
| 1       | 0       | 1      | 0        |
| 1       | 1       | 0      | 1        |

관찰:
- **합** $s$: 둘 중 하나만 1일 때 1 → **XOR**! $s = x \oplus y$
- **올림수** $c$: 둘 다 1일 때만 1 → **AND**! $c = xy$

```lean
-- 반가산기: (합, 올림수) 쌍을 출력
def halfAdder (x y : Bool) : Bool × Bool :=
  (xor x y, x && y)

-- 검증
#eval halfAdder false false  -- (false, false) = (0, 0)
#eval halfAdder false true   -- (true, false)  = (1, 0)
#eval halfAdder true false   -- (true, false)  = (1, 0)
#eval halfAdder true true    -- (false, true)  = (0, 1)

-- 정확성 증명: 반가산기의 출력이 실제 덧셈과 일치
-- x + y = c * 2 + s (이진수로)
example : ∀ x y : Bool,
  let (s, c) := halfAdder x y
  (if x then 1 else 0) + (if y then 1 else 0)
    = (if c then 2 else 0) + (if s then 1 else 0) := by decide
```

### 5.2 전가산기 (Full Adder)

**전가산기**(full adder)는 아래 자리에서 올라오는 **올림수**($c_i$)까지 포함하여 3개의 비트를 더한다.

| $x$ | $y$ | $c_i$ | 합 $s$ | 올림수 $c_{i+1}$ |
|-----|-----|-------|--------|----------------|
| 0   | 0   | 0     | 0      | 0 |
| 0   | 0   | 1     | 1      | 0 |
| 0   | 1   | 0     | 1      | 0 |
| 0   | 1   | 1     | 0      | 1 |
| 1   | 0   | 0     | 1      | 0 |
| 1   | 0   | 1     | 0      | 1 |
| 1   | 1   | 0     | 0      | 1 |
| 1   | 1   | 1     | 1      | 1 |

- **합**: $s = x \oplus y \oplus c_i$ (3개의 XOR)
- **올림수**: $c_{i+1} = xy + xc_i + yc_i$ (3개 중 2개 이상이 1일 때) — 다수결 투표기와 같다!

```lean
-- 전가산기: 반가산기 2개로 구현
def fullAdder (x y ci : Bool) : Bool × Bool :=
  let (s1, c1) := halfAdder x y       -- 1단계: x와 y를 더한다
  let (s, c2) := halfAdder s1 ci      -- 2단계: 중간 합과 올림수를 더한다
  (s, c1 || c2)                        -- 최종 올림수는 두 올림수의 OR

-- 검증: 모든 경우
#eval fullAdder false false false  -- (false, false) = 0+0+0 = 0
#eval fullAdder true true false    -- (false, true)  = 1+1+0 = 10₂
#eval fullAdder true true true     -- (true, true)   = 1+1+1 = 11₂

-- 정확성 증명: x + y + ci = c_{i+1} * 2 + s
example : ∀ x y ci : Bool,
  let (s, co) := fullAdder x y ci
  (if x then 1 else 0) + (if y then 1 else 0) + (if ci then 1 else 0)
    = (if co then 2 else 0) + (if s then 1 else 0) := by decide
```

### 5.3 n비트 가산기 — 리플 캐리 가산기

여러 비트의 두 수를 더하려면, 전가산기를 **체인**처럼 연결한다. 한 자리의 올림수가 다음 자리의 입력이 된다.

```lean
-- n비트 리플 캐리 가산기
-- 입력: 두 비트열 (최하위 비트부터)과 초기 올림수
-- 출력: 결과 비트열과 최종 올림수
def rippleCarryAdder : List Bool → List Bool → Bool → List Bool × Bool
  | [], [], carry => ([], carry)
  | x :: xs, y :: ys, carry =>
    let (s, co) := fullAdder x y carry
    let (rest, finalCarry) := rippleCarryAdder xs ys co
    (s :: rest, finalCarry)
  | _, _, carry => ([], carry)  -- 길이가 다른 경우 (단순화)

-- 예시: 5 + 3 = 8
-- 5 = 101₂ (LSB first: [true, false, true])
-- 3 = 011₂ (LSB first: [true, true, false])
-- 8 = 1000₂ (LSB first: [false, false, false], carry = true)
#eval rippleCarryAdder [true, false, true] [true, true, false] false
-- ([false, false, false], true) → 1000₂ = 8 ✓
```

### 5.4 Rosen 그림 10: 3비트 가산기

두 개의 3비트 정수 $(x_2 x_1 x_0)_2$와 $(y_2 y_1 y_0)_2$를 더하여 $(s_3 s_2 s_1 s_0)_2$를 출력:

```
          x₀ y₀        x₁ y₁        x₂ y₂
           │  │          │  │          │  │
        ┌──┴──┴──┐   ┌──┴──┴──┐   ┌──┴──┴──┐
   0 ───┤ 반가산기├───┤ 전가산기├───┤ 전가산기├── c₂ = s₃
        └───┬────┘   └───┬────┘   └───┬────┘
            s₀            s₁            s₂
```

```lean
-- 3비트 덧셈기
def adder3bit (x2 x1 x0 y2 y1 y0 : Bool) : Bool × Bool × Bool × Bool :=
  let (s0, c0) := halfAdder x0 y0
  let (s1, c1) := fullAdder x1 y1 c0
  let (s2, c2) := fullAdder x2 y2 c1
  (c2, s2, s1, s0)  -- (s3, s2, s1, s0)

-- 예시: 5(101) + 3(011) = 8(1000)
#eval adder3bit true false true false true true
-- (true, false, false, false) = 1000₂ = 8 ✓

-- 예시: 7(111) + 1(001) = 8(1000)
#eval adder3bit true true true false false true
-- (true, false, false, false) = 1000₂ = 8 ✓

-- 정확성 증명: 모든 3비트 입력에 대해 올바른 결과
-- (수가 너무 많으므로 decide로 자동 확인)
example : ∀ x2 x1 x0 y2 y1 y0 : Bool,
  let (s3, s2, s1, s0) := adder3bit x2 x1 x0 y2 y1 y0
  let xVal := (if x2 then 4 else 0) + (if x1 then 2 else 0) + (if x0 then 1 else 0)
  let yVal := (if y2 then 4 else 0) + (if y1 then 2 else 0) + (if y0 then 1 else 0)
  let sVal := (if s3 then 8 else 0) + (if s2 then 4 else 0) +
              (if s1 then 2 else 0) + (if s0 then 1 else 0)
  xVal + yVal = sVal := by decide
```

> 🎉 **이것이 형식 검증의 힘이다!** 3비트 가산기가 $2^6 = 64$가지 모든 입력에 대해 올바르게 동작함을 `decide` 한 방으로 증명했다!

---

## 6. 연습문제: 괄호 채우기 (Skeleton)

### 연습 6.1: 회로 출력 구하기

```lean
-- 회로 1: x AND (NOT y)
def circuit1 (x y : Bool) : Bool := x && ⟨YOUR_EXPRESSION⟩

-- 검증: circuit1 true true = ?
example : circuit1 true true = ⟨YOUR_ANSWER⟩ := by rfl

-- 회로 2: (x OR y) AND (NOT x)
def circuit2 (x y : Bool) : Bool := (x || y) && ⟨YOUR_EXPRESSION⟩

-- 검증: circuit2 true false = ?
example : circuit2 true false = ⟨YOUR_ANSWER⟩ := by rfl
```

<details>
<summary>📝 답 보기</summary>

```lean
def circuit1 (x y : Bool) : Bool := x && (!y)
example : circuit1 true true = false := by rfl

def circuit2 (x y : Bool) : Bool := (x || y) && (!x)
example : circuit2 true false = false := by rfl
-- circuit2 false true = true ((!false) = true, (false || true) && true = true)
```

</details>

### 연습 6.2: 반가산기의 합(sum) 함수

```lean
-- 반가산기의 합(sum)은 XOR이다.
-- XOR을 AND, OR, NOT만으로 표현하라:
-- 힌트: x ⊕ y = (x + y) · ¬(xy) = (x || y) && !(x && y)
def xorFromGates (x y : Bool) : Bool := (x || y) && ⟨YOUR_EXPRESSION⟩

-- 검증
example : ∀ x y : Bool, xorFromGates x y = xor x y := by ⟨YOUR_TACTIC⟩
```

<details>
<summary>📝 답 보기</summary>

```lean
def xorFromGates (x y : Bool) : Bool := (x || y) && (!(x && y))

example : ∀ x y : Bool, xorFromGates x y = xor x y := by decide
```

</details>

### 연습 6.3: 전가산기 직접 구현

```lean
-- 전가산기를 반가산기 없이 직접 부울 식으로 구현하라
-- s = x ⊕ y ⊕ ci
-- co = xy + xci + yci (다수결)
def fullAdder_direct (x y ci : Bool) : Bool × Bool :=
  let s := xor (xor x y) ⟨YOUR_EXPRESSION⟩
  let co := (x && y) || (x && ci) || ⟨YOUR_EXPRESSION⟩
  (s, co)

-- 원래 fullAdder와 동치 확인
example : ∀ x y ci : Bool,
  fullAdder_direct x y ci = fullAdder x y ci := by ⟨YOUR_TACTIC⟩
```

<details>
<summary>📝 답 보기</summary>

```lean
def fullAdder_direct (x y ci : Bool) : Bool × Bool :=
  let s := xor (xor x y) ci
  let co := (x && y) || (x && ci) || (y && ci)
  (s, co)

example : ∀ x y ci : Bool,
  fullAdder_direct x y ci = fullAdder x y ci := by decide
```

</details>

---

## 7. 연습문제: `sorry`로 직접 증명하기 (도전)

### 연습 7.1: 다수결 투표기가 정확함을 증명

```lean
-- majorityVote가 "2명 이상 찬성"일 때만 true를 반환함을 증명하라
-- decide를 사용하지 않고 cases로 증명해 보라
example : ∀ x y z : Bool, majorityVote x y z = atLeastTwo x y z := by
  sorry
```

<details>
<summary>📝 답 보기</summary>

```lean
example : ∀ x y z : Bool, majorityVote x y z = atLeastTwo x y z := by
  intro x y z
  cases x <;> cases y <;> cases z <;> rfl
```

$2^3 = 8$가지 경우 모두 확인하면 양변이 계산적으로 같다.

</details>

### 연습 7.2: 반감산기 설계

**반감산기**(half subtractor)는 두 비트 $x, y$를 입력받아 뺄셈 결과 $d$(difference)와 내림수 $b$(borrow)를 출력한다.

| $x$ | $y$ | 차 $d$ | 내림수 $b$ |
|-----|-----|--------|----------|
| 0   | 0   | 0      | 0 |
| 0   | 1   | 1      | 1 (아래서 빌려옴) |
| 1   | 0   | 1      | 0 |
| 1   | 1   | 0      | 0 |

```lean
-- 반감산기를 구현하고 정확성을 증명하라
-- 힌트: d = x ⊕ y (합과 같다!), b = (NOT x) AND y
def halfSubtractor (x y : Bool) : Bool × Bool :=
  sorry

-- 정확성: x - y = (결과) - 2*(내림수)
-- 즉, (if x then 1 else 0) - (if y then 1 else 0)
--    = (if d then 1 else 0) - (if b then 2 else 0)
```

<details>
<summary>📝 답 보기</summary>

```lean
def halfSubtractor (x y : Bool) : Bool × Bool :=
  (xor x y, !x && y)

#eval halfSubtractor false false  -- (false, false) = (0, 0)
#eval halfSubtractor false true   -- (true, true)   = (1, 1) → 0-1 = 1-2 = -1
#eval halfSubtractor true false   -- (true, false)  = (1, 0) → 1-0 = 1
#eval halfSubtractor true true    -- (false, false) = (0, 0) → 1-1 = 0

-- 정확성 증명
example : ∀ x y : Bool,
  let (d, b) := halfSubtractor x y
  (if x then 1 else 0 : Int) - (if y then 1 else 0)
    = (if d then 1 else 0) - (if b then 2 else 0) := by decide
```

</details>

### 연습 7.3: 4-스위치 조명 제어 (연습문제 8)

```lean
-- 4개의 스위치로 조명을 제어하는 회로를 설계하라.
-- 어느 하나의 스위치 상태를 바꾸면 조명이 반전된다.
-- 초기: 모두 닫힘(1), 조명 켜짐(1)
-- 패턴: 1의 개수가 홀수이면 켜짐, 짝수이면 꺼짐... 이 아니라
-- 실제로는 XOR 패턴이다!

def lightSwitch4 (w x y z : Bool) : Bool := sorry

-- 검증: 초기 상태
example : lightSwitch4 true true true true = true := by rfl
-- 하나 바꿈
example : lightSwitch4 true true true false = false := by rfl
```

<details>
<summary>📝 답 보기</summary>

```lean
-- 4-스위치 조명: XOR 체인
def lightSwitch4 (w x y z : Bool) : Bool := xor (xor (xor w x) y) z

-- 또는 곱의 합 표준형으로 (매우 길다):
-- 1의 개수가 홀수(1개 또는 3개)일 때 조명이 켜진다.
-- 하지만 초기(1,1,1,1)=1이고 4개=짝수, 이상하다?
-- 다시 확인: 초기(1,1,1,1)→1, 하나 바꿈(1,1,1,0)→0, 또 하나 바꿈(1,1,0,0)→1
-- 이것은 "바뀐 횟수가 짝수이면 1" = XOR 체인

example : lightSwitch4 true true true true = true := by rfl
example : lightSwitch4 true true true false = false := by rfl
example : lightSwitch4 true true false false = true := by rfl
example : lightSwitch4 false false false false = true := by rfl
-- 아! false false false false에서 1의 개수=0(짝수)→1
-- true true true true에서 1의 개수=4(짝수)→1
-- 즉 "짝수 개의 1이면 켜짐" ← 이것은 XOR의 NOT

-- 수정: 실제로는 XNOR 체인이어야 한다
def lightSwitch4_correct (w x y z : Bool) : Bool :=
  !(xor (xor (xor w x) y) z)

example : lightSwitch4_correct true true true true = true := by rfl
example : lightSwitch4_correct true true true false = false := by rfl
example : lightSwitch4_correct true true false false = true := by rfl

-- 하지만 XOR(1,1,1,1) = 0이므로 NOT하면 1 ✓
-- XOR(1,1,1,0) = 1이므로 NOT하면 0 ✓
```

사실 "1의 개수가 짝수이면 조명이 켜진다"는 규칙은 $\overline{w \oplus x \oplus y \oplus z}$와 같다.

</details>

---

## 8. 다중 출력 회로와 조합 회로의 깊이

### 8.1 다중 출력 회로

반가산기와 전가산기처럼 **출력이 여러 개**인 회로를 **다중 출력 회로**(multiple output circuit)라 한다. Lean 4에서는 **튜플**(tuple)로 자연스럽게 표현된다:

```lean
-- 단일 출력: Bool
def singleOutput (x y : Bool) : Bool := x && y

-- 다중 출력: Bool × Bool
def multiOutput (x y : Bool) : Bool × Bool := (xor x y, x && y)
```

### 8.2 회로의 깊이

**깊이**(depth)는 입력에서 출력까지의 최대 게이트 수이다. 깊이가 작을수록 회로가 빠르다.

- 인버터, OR, AND 게이트 각각의 깊이 = 1
- 반가산기: 깊이 2 (AND/OR 한 번 + 게이트 한 번)
- 전가산기: 깊이 4 (반가산기 2개 + OR 1개)
- n비트 리플 캐리 가산기: 깊이 $O(n)$ (올림수가 순차적으로 전파)

---

## 9. 핵심 요약

| 개념 | 핵심 | Lean 4 |
|------|------|--------|
| **인버터** | NOT 게이트 | `!x` |
| **OR 게이트** | 하나라도 1이면 1 | `x \|\| y` |
| **AND 게이트** | 둘 다 1이어야 1 | `x && y` |
| **조합 회로** | 기억 없음, 입력→출력 | 순수 함수 |
| **반가산기** | 1비트 + 1비트 = (합, 올림수) | `(xor x y, x && y)` |
| **전가산기** | 반가산기 2개 체인 | 3입력 → (합, 올림수) |
| **다수결 투표기** | xy + xz + yz | 2개 이상 1이면 1 |
| **형식 검증** | 사양과 구현의 동치 증명 | `decide` |

---

## 다음 파트 예고

**Part 14-D**에서는:
- **회로의 최소화**(minimization): 불필요한 게이트 줄이기
- **카르노맵**(Karnaugh map): 2~4변수 부울 식 간소화
- **퀸-맥클러스키 방법**(Quine-McCluskey): 체계적 최소화 알고리즘
- **프라임 임플리컨트**와 **에센셜 프라임 임플리컨트**
- 무정의 조건(Don't Care)을 활용한 최적화
