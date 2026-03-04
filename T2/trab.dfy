class {:autocontracts} DequeCircular {
  var a: array<int>
  var head: nat
  var tail: nat
  var size: nat

  ghost var Content: seq<int>

  // Invariante de classe (via predicate):
  // Utilizar um predicado Valid() adequado para a invariante da representação abstrata associada à coleção do tipo deque circular.
  ghost predicate Valid()
    reads this, a
  {
    a.Length > 0
    && 0 <= size <= a.Length
    && 0 <= head < a.Length
    && 0 <= tail < a.Length
    && |Content| == size
    && tail == (head + size) % a.Length
  }

  // Construtor deve instanciar um deque circular vazio com um determinado tamanho máximo.
  constructor(max: nat)
    requires max > 0
    ensures Content == []
    ensures size == 0
    ensures a.Length == max
  {
    a := new int[max];
    head := 0;
    tail := 0;
    size := 0;
    Content := [];
  }

  // Adicionar um novo elemento ao final do deque.
  method PushBack(x: int)
    requires size < a.Length
    modifies this, a
    ensures Content == old(Content) + [x]
  {
    a[tail] := x;
    tail := (tail + 1) % a.Length;
    size := size + 1;
    Content := old(Content) + [x];

    assert tail == (head + size) % a.Length;
    assert |Content| == size;
  }

  // Adicionar um novo elemento ao início do deque.
  method PushFront(x: int)
    requires size < a.Length
    modifies this, a
    ensures Content == [x] + old(Content)
  {
    head := (head + a.Length - 1) % a.Length;
    a[head] := x;
    size := size + 1;
    Content := [x] + old(Content);

    assert tail == (head + size) % a.Length;
    assert |Content| == size;
  }

  // Remover um elemento do final do deque e retornar seu valor.
  method PopBack() returns (v: int)
    requires size > 0
    modifies this, a
    ensures Content == old(Content[.. |Content| - 1])
  {
    tail := (tail + a.Length - 1) % a.Length;
    v := a[tail];
    size := size - 1;
    Content := old(Content[.. |Content| - 1]);

    assert tail == (head + size) % a.Length;
    assert |Content| == size;
  }

  // Remover um elemento do início do deque e retornar seu valor.
  method PopFront() returns (v: int)
    requires size > 0
    modifies this, a
    ensures Content == old(Content[1..])
  {
    v := a[head];
    head := (head + 1) % a.Length;
    size := size - 1;
    Content := old(Content[1..]);

    assert tail == (head + size) % a.Length;
    assert |Content| == size;
  }

  // Verificar se um determinado elemento pertence ou não ao deque.
  ghost function Contains(x: int): bool
    reads this, Repr
  {
    x in Content
  }

  // Retornar o número de elementos do deque.
  function Size(): nat
    reads this, Repr
    ensures Size() == size
    ensures Size() == |Content|
  {
    size
  }

  // Retornar a capacidade máxima do deque.
  function Capacity(): nat
    reads this, Repr
  {
    a.Length
  }

  // Verificar se o deque está vazio ou não.
  function IsEmpty(): bool
    reads this, Repr
  {
    size == 0
  }

  // Verificar se o deque está cheio ou não.
  function IsFull(): bool
    reads this, Repr
  {
    size == a.Length
  }

  // Redimensionar o deque para um tamanho maior.
  method Resize(newCapacity: nat)
    requires newCapacity > a.Length
    modifies this, a
    ensures a.Length == newCapacity
    ensures Content == old(Content)
  {
    var oldA := a;
    var oldHead := head;
    var oldSize := size;
    var oldLen := a.Length;

    var newA := new int[newCapacity];

    var i := 0;
    while i < oldSize
      invariant 0 <= i <= oldSize
      invariant newA.Length == newCapacity
      invariant a == oldA
      invariant head == oldHead
      invariant size == oldSize
      invariant a.Length == oldLen
      invariant forall j :: 0 <= j < i ==> newA[j] == oldA[(oldHead + j) % oldLen]
      decreases oldSize - i
    {
      newA[i] := oldA[(oldHead + i) % oldLen];
      i := i + 1;
    }

    a := newA;
    head := 0;
    tail := oldSize;

    assert a.Length == newCapacity;
    assert a.Length > 0;
    assert 0 <= size <= a.Length;
    assert 0 <= head < a.Length;
    assert 0 <= tail < a.Length;
    assert tail == (head + size) % a.Length;
  }
}

method Main()
{
  // Dafny v4.0.0
  // Integrantes:
  //  Carolina Ferreira 
  //  , Felipe Freitas 
  //  , Luiza Heller 
  //  , Mateus Caçabuena

  var d := new DequeCircular(5);
  assert d.Content == [];
  assert d.Size() == 0;
  assert d.Capacity() == 5;
  assert d.IsEmpty();

  d.PushBack(10);
  d.PushBack(20);
  assert d.Content == [10, 20];
  assert d.Size() == 2;

  d.PushFront(5);
  assert d.Content == [5, 10, 20];
  assert d.Size() == 3;

  var x := d.PopFront();
  assert x == 5;
  assert d.Content == [10, 20];

  var y := d.PopBack();
  assert y == 20;
  assert d.Content == [10];
  assert d.Size() == 1;

  d.PushBack(30);
  d.PushBack(40);
  d.PushBack(50);
  d.PushBack(60);
  assert d.Content == [10, 30, 40, 50, 60];
  assert d.IsFull();

  d.Resize(10);
  assert d.Capacity() == 10;
  assert d.Content == [10, 30, 40, 50, 60];
  assert !d.IsFull();
}