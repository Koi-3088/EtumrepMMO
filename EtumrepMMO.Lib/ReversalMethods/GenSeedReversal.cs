using Microsoft.Z3;
using PKHeX.Core;

namespace EtumrepMMO.Lib;

/// <summary>
/// Reverses for middle step seeds by using Z3 to calculate.
/// </summary>
public static class GenSeedReversal
{
    private static readonly Context ctx = new(new Dictionary<string, string> { { "model", "true" } });

    /// <summary>
    /// Middle level seed calculation for the Generator Seed
    /// </summary>
    /// <param name="seed">Bottom level Entity seed.</param>
    public static IEnumerable<ulong> FindPotentialGenSeeds(ulong seed)
    {
        using var genSeedResult = ctx.MkBVConst("s0", 64); ;
        using var genSeedExpression = GetBaseGenSeedModel(genSeedResult);
        var exp = CreateGenSeedModel(seed, genSeedExpression);

        // Z3 is a theorem prover, and only proves if the model can be solved.
        // To yield multiple possible values from the expression, we must re-evaluate with added constraints.
        // Add each previously valid result as an "and this must not be a result".
        // Yield until no results found.
        while (Check(exp) is { } m)
        {
            foreach (var kvp in m.Consts) // should only be 1
            {
                var tmp = (BitVecNum)kvp.Value;
                var possible = tmp.UInt64;
                yield return possible;

                // Force the model to ignore the above result for s0, so we may get a new result if any.
                using var constraint = ctx.MkNot(ctx.MkEq(genSeedResult, tmp));
                exp = ctx.MkAnd(exp, constraint);
            }
            m.Dispose();
        }
        exp.Dispose();
    }

    private static BoolExpr CreateGenSeedModel(ulong seed, BitVecExpr genSeedExpression)
    {
        using var real_seed = ctx.MkBV(seed, 64);
        return ctx.MkEq(real_seed, genSeedExpression);
    }

    private static BitVecExpr GetBaseGenSeedModel(BitVecExpr genSeedResult)
    {
        BitVecExpr s0 = genSeedResult;
        BitVecExpr s1 = ctx.MkBV(Xoroshiro128Plus.XOROSHIRO_CONST, 64);

        // var slotRand = ctx.MkBVAdd(s0, s1);
        s1 = ctx.MkBVXOR(s0, s1);
        using var tmp = ctx.MkBVRotateLeft(24, s0);
        using var tmp2 = ctx.MkBV(1 << 16, 64);
        s0 = ctx.MkBVXOR(tmp, ctx.MkBVXOR(s1, ctx.MkBVMul(s1, tmp2)));
        s1 = ctx.MkBVRotateLeft(37, s1);
        return ctx.MkBVAdd(s0, s1); // genSeed
        // no rot/xor needed, the add result is enough.
    }

    private static Model? Check(BoolExpr cond)
    {
        using Solver solver = ctx.MkSolver();
        solver.Assert(cond);
        Status q = solver.Check();
        if (q != Status.SATISFIABLE)
            return null;
        return solver.Model;
    }
}
