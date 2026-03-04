class {:autocontracts} Fila
{
    //abstração
    ghost var Conteudo: seq<int>

    //implementação
    var a: array<int>
    var tamanho: nat

    //invariante de classe
    ghost predicate Valid()
    {
        && a.Length > 0
        && 0 <= tamanho <= a.Length
        && Conteudo == a[..tamanho]
    }

    constructor ()
    ensures Conteudo == []
    {
        a := new int[5];
        tamanho := 0;
        Conteudo := [];
    }

    function Quantidade():nat
    ensures Quantidade() == |Conteudo|
    {
        tamanho
    }

    method Enfileirar(e:int)
    ensures Conteudo == old(Conteudo) + [e]
    {
        if tamanho == a.Length
        {
            var b := new int[2*a.Length];
            forall i | 0 <= i < a.Length
            {
                b[i] := a[i];
            }
            a := b;
        }
        a[tamanho] := e;
        tamanho := tamanho+1;
        Conteudo := Conteudo + [e];
    }

    method Desenfileirar() returns (e:int)
    requires |Conteudo| > 0
    ensures e == old(Conteudo[0])
    ensures Conteudo == old(Conteudo[1..])
    {
        e := a[0];
        tamanho := tamanho - 1;
        Conteudo := Conteudo[1..];
        forall i | 0 <= i < tamanho
        {
            a[i] := a[i+1];
        }
        //Conteudo := a[..tamanho];
    }
}

method Main()
{
    var f := new Fila();
    assert f.Conteudo == [];
    assert f.Quantidade() == 0;
    f.Enfileirar(1);
    assert f.Conteudo == [1];
    assert f.Quantidade() == 1;
    f.Enfileirar(2);
    assert f.Conteudo == [1,2];
    assert f.Quantidade() == 2;
    var e := f.Desenfileirar();
    assert e == 1;
    assert f.Conteudo == [2];
    assert f.Quantidade() == 1;
}