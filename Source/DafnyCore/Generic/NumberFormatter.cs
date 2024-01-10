// Copyright by the contributors to the Dafny Project
// SPDX-License-Identifier: MIT

using System.Collections.Generic;
using System.Diagnostics.Contracts;
using System.Numerics;


namespace Microsoft.Dafny {
  public class NumberFormatter {
    public static bool IsNearRoundBigHexNumber(BigInteger n, out bool nearZero) {
      if (n < 0) {
        n = -n;
      }
      nearZero = n < 0x5000;
      var diff = n % 0x100;
      return diff < 5 || (0x100 - 5) < diff;
    }

    public static string DecimalWithDelimiters(BigInteger n) {
      return n < 0 ? "-" + DecimalWithDelimitersFromNatural(-n) : DecimalWithDelimitersFromNatural(n);
    }

    private static string DecimalWithDelimitersFromNatural(BigInteger n) {
      Contract.Requires(0 <= n);
      var s = n.ToString();
      if (n < 10_000) {
        return s;
      }
      return InsertDelimiters(s, "_", 3);
    }

    public static string HexWithDelimiters(BigInteger n) {
      return n < 0 ? "-0x" + HexWithDelimitersFromNatural(-n) : "0x" + HexWithDelimitersFromNatural(n);
    }

    private static string HexWithDelimitersFromNatural(BigInteger n) {
      Contract.Requires(0 <= n);
      var nOrig = n;
      var s = "";
      while (0 < n) {
        var digit = (int)(n % 16);
        var hexDigit = digit < 10 ? (char)('0' + digit) : (char)('A' + digit - 10);
        s = $"{hexDigit}{s}";
        n /= 16;
      }
      if (s == "") {
        s = "0";
      }
      if (nOrig < 0x10_000) {
        return s;
      }
      return InsertDelimiters(s, "_", 4);
    }

    public static string InsertDelimiters(string s, string delimiter, int spacing) {
      var r = "";
      foreach (var piece in ChopFromRight(s, spacing)) {
        r = r == "" ? piece : $"{piece}{delimiter}{r}";
      }
      return r;
    }

    public static IEnumerable<string> ChopFromRight(string s, int size) {
      Contract.Requires(0 < size);
      var position = s.Length - size;
      while (0 < position) {
        yield return s.Substring(position, size);
        position -= size;
      }
      yield return s.Substring(0, position + size);
    }
  }
}
