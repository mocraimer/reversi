// Dafny program reversiMain.dfy compiled into C#
// To recompile, use 'csc' with: /r:System.Numerics.dll
// and choosing /target:exe or /target:library
// You might also want to include compiler switches like:
//     /debug /nowarn:0164 /nowarn:0219

using System; // for Func
using System.Numerics;

namespace Dafny
{
  using System.Collections.Generic;
// set this option if you want to use System.Collections.Immutable and if you know what you're doing.
#if DAFNY_USE_SYSTEM_COLLECTIONS_IMMUTABLE
  using System.Collections.Immutable;
  using System.Linq;

  public class Set<T>
  {
    readonly ImmutableHashSet<T> setImpl;
    Set(ImmutableHashSet<T> d) {
      this.setImpl = d;
    }
    public static readonly Set<T> Empty = new Set<T>(ImmutableHashSet<T>.Empty);
    public static Set<T> FromElements(params T[] values) {
      return FromElements((IEnumerable<T>)values);
    }
    public static Set<T> FromElements(IEnumerable<T> values) {
      var d = ImmutableHashSet<T>.Empty.ToBuilder();
      foreach (T t in values)
        d.Add(t);
      return new Set<T>(d.ToImmutable());
    }
    public static Set<T> FromCollection(ICollection<T> values) {
      var d = ImmutableHashSet<T>.Empty.ToBuilder();
      foreach (T t in values)
        d.Add(t);
      return new Set<T>(d.ToImmutable());
    }
    public int Length {
      get { return this.setImpl.Count; }
    }
    public long LongLength {
      get { return this.setImpl.Count; }
    }
    public IEnumerable<T> Elements {
      get {
        return this.setImpl;
      }
    }
    /// <summary>
    /// This is an inefficient iterator for producing all subsets of "this".  Each set returned is the same
    /// Set<T> object (but this Set<T> object is fresh; in particular, it is not "this").
    /// </summary>
    public IEnumerable<Set<T>> AllSubsets {
      get {
        // Start by putting all set elements into a list
        var elmts = new List<T>();
        elmts.AddRange(this.setImpl);
        var n = elmts.Count;
        var which = new bool[n];
        var s = ImmutableHashSet<T>.Empty.ToBuilder();
        while (true) {
          yield return new Set<T>(s.ToImmutable());
          // "add 1" to "which", as if doing a carry chain.  For every digit changed, change the membership of the corresponding element in "s".
          int i = 0;
          for (; i < n && which[i]; i++) {
            which[i] = false;
            s.Remove(elmts[i]);
          }
          if (i == n) {
            // we have cycled through all the subsets
            break;
          }
          which[i] = true;
          s.Add(elmts[i]);
        }
      }
    }
    public bool Equals(Set<T> other) {
        return this.setImpl.SetEquals(other.setImpl);
    }
    public override bool Equals(object other) {
        var otherSet = other as Set<T>;
        return otherSet != null && this.Equals(otherSet);
    }
    public override int GetHashCode() {
      var hashCode = 1;
      foreach (var t in this.setImpl) {
        hashCode = hashCode * (t.GetHashCode()+3);
      }
      return hashCode;
    }
    public override string ToString() {
      var s = "{";
      var sep = "";
      foreach (var t in this.setImpl) {
        s += sep + t.ToString();
        sep = ", ";
      }
      return s + "}";
    }
    public bool IsProperSubsetOf(Set<T> other) {
        return IsProperSubsetOf(other);
    }
    public bool IsSubsetOf(Set<T> other) {
        return IsSubsetOf(other);
    }
    public bool IsSupersetOf(Set<T> other) {
      return other.IsSupersetOf(this);
    }
    public bool IsProperSupersetOf(Set<T> other) {
      return other.IsProperSupersetOf(this);
    }
    public bool IsDisjointFrom(Set<T> other) {
      ImmutableHashSet<T> a, b;
      if (this.setImpl.Count < other.setImpl.Count) {
        a = this.setImpl; b = other.setImpl;
      } else {
        a = other.setImpl; b = this.setImpl;
      }
      foreach (T t in a) {
        if (b.Contains(t))
          return false;
      }
      return true;
    }
    public bool Contains(T t) {
      return this.setImpl.Contains(t);
    }
    public Set<T> Union(Set<T> other) {
        return new Set<T>(this.setImpl.Union(other.setImpl));
    }
    public Set<T> Intersect(Set<T> other) {
      return new Set<T>(this.setImpl.Intersect(other.setImpl));
    }
    public Set<T> Difference(Set<T> other) {
        return new Set<T>(this.setImpl.Except(other.setImpl));
    }
  }
  public partial class MultiSet<T>
  {

    readonly ImmutableDictionary<T, int> dict;
    MultiSet(ImmutableDictionary<T, int> d) {
      dict = d;
    }
    public static readonly MultiSet<T> Empty = new MultiSet<T>(ImmutableDictionary<T, int>.Empty);
    public static MultiSet<T> FromElements(params T[] values) {
      var d = ImmutableDictionary<T, int>.Empty.ToBuilder();
      foreach (T t in values) {
        var i = 0;
        if (!d.TryGetValue(t, out i)) {
          i = 0;
        }
        d[t] = i + 1;
      }
      return new MultiSet<T>(d.ToImmutable());
    }
    public static MultiSet<T> FromCollection(ICollection<T> values) {
      var d = ImmutableDictionary<T, int>.Empty.ToBuilder();
      foreach (T t in values) {
        var i = 0;
        if (!d.TryGetValue(t, out i)) {
          i = 0;
        }
        d[t] = i + 1;
      }
      return new MultiSet<T>(d.ToImmutable());
    }
    public static MultiSet<T> FromSeq(Sequence<T> values) {
      var d = ImmutableDictionary<T, int>.Empty.ToBuilder();
      foreach (T t in values.Elements) {
        var i = 0;
        if (!d.TryGetValue(t, out i)) {
          i = 0;
        }
        d[t] = i + 1;
      }
      return new MultiSet<T>(d.ToImmutable());
    }
    public static MultiSet<T> FromSet(Set<T> values) {
      var d = ImmutableDictionary<T, int>.Empty.ToBuilder();
      foreach (T t in values.Elements) {
        d[t] = 1;
      }
      return new MultiSet<T>(d.ToImmutable());
    }

    public bool Equals(MultiSet<T> other) {
      return other.IsSubsetOf(this) && this.IsSubsetOf(other);
    }
    public override bool Equals(object other) {
      return other is MultiSet<T> && Equals((MultiSet<T>)other);
    }
    public override int GetHashCode() {
      var hashCode = 1;
      foreach (var kv in dict) {
        var key = kv.Key.GetHashCode();
        key = (key << 3) | (key >> 29) ^ kv.Value.GetHashCode();
        hashCode = hashCode * (key + 3);
      }
      return hashCode;
    }
    public override string ToString() {
      var s = "multiset{";
      var sep = "";
      foreach (var kv in dict) {
        var t = kv.Key.ToString();
        for (int i = 0; i < kv.Value; i++) {
          s += sep + t.ToString();
          sep = ", ";
        }
      }
      return s + "}";
    }
    public bool IsProperSubsetOf(MultiSet<T> other) {
      return !Equals(other) && IsSubsetOf(other);
    }
    public bool IsSubsetOf(MultiSet<T> other) {
      foreach (T t in dict.Keys) {
        if (!other.dict.ContainsKey(t) || other.dict[t] < dict[t])
          return false;
      }
      return true;
    }
    public bool IsSupersetOf(MultiSet<T> other) {
      return other.IsSubsetOf(this);
    }
    public bool IsProperSupersetOf(MultiSet<T> other) {
      return other.IsProperSubsetOf(this);
    }
    public bool IsDisjointFrom(MultiSet<T> other) {
      foreach (T t in dict.Keys) {
        if (other.dict.ContainsKey(t))
          return false;
      }
      foreach (T t in other.dict.Keys) {
        if (dict.ContainsKey(t))
          return false;
      }
      return true;
    }
    public bool Contains(T t) {
      return dict.ContainsKey(t);
    }
    public MultiSet<T> Union(MultiSet<T> other) {
      if (dict.Count == 0)
        return other;
      else if (other.dict.Count == 0)
        return this;
        var r = ImmutableDictionary<T, int>.Empty.ToBuilder();
      foreach (T t in dict.Keys) {
        var i = 0;
        if (!r.TryGetValue(t, out i)) {
          i = 0;
        }
        r[t] = i + dict[t];
      }
      foreach (T t in other.dict.Keys) {
        var i = 0;
        if (!r.TryGetValue(t, out i)) {
          i = 0;
        }
        r[t] = i + other.dict[t];
      }
      return new MultiSet<T>(r.ToImmutable());
    }
    public MultiSet<T> Intersect(MultiSet<T> other) {
      if (dict.Count == 0)
        return this;
      else if (other.dict.Count == 0)
        return other;
      var r = ImmutableDictionary<T, int>.Empty.ToBuilder();
      foreach (T t in dict.Keys) {
        if (other.dict.ContainsKey(t)) {
          r[t] = other.dict[t] < dict[t] ? other.dict[t] : dict[t];
        }
      }
      return new MultiSet<T>(r.ToImmutable());
    }
    public MultiSet<T> Difference(MultiSet<T> other) { // \result == this - other
      if (dict.Count == 0)
        return this;
      else if (other.dict.Count == 0)
        return this;
      var r = ImmutableDictionary<T, int>.Empty.ToBuilder();
      foreach (T t in dict.Keys) {
        if (!other.dict.ContainsKey(t)) {
          r[t] = dict[t];
        } else if (other.dict[t] < dict[t]) {
          r[t] = dict[t] - other.dict[t];
        }
      }
      return new MultiSet<T>(r.ToImmutable());
    }
    public IEnumerable<T> Elements {
      get {
        foreach (T t in dict.Keys) {
          int n;
          dict.TryGetValue(t, out n);
          for (int i = 0; i < n; i ++) {
            yield return t;
          }
        }
      }
    }
  }

  public partial class Map<U, V>
  {
    readonly ImmutableDictionary<U, V> dict;
    Map(ImmutableDictionary<U, V> d) {
      dict = d;
    }
    public static readonly Map<U, V> Empty = new Map<U, V>(ImmutableDictionary<U, V>.Empty);
    public static Map<U, V> FromElements(params Pair<U, V>[] values) {
      var d = ImmutableDictionary<U, V>.Empty.ToBuilder();
      foreach (Pair<U, V> p in values) {
        d[p.Car] = p.Cdr;
      }
      return new Map<U, V>(d.ToImmutable());
    }
    public static Map<U, V> FromCollection(List<Pair<U, V>> values) {
      var d = ImmutableDictionary<U, V>.Empty.ToBuilder();
      foreach (Pair<U, V> p in values) {
        d[p.Car] = p.Cdr;
      }
      return new Map<U, V>(d.ToImmutable());
    }
    public int Length {
      get { return dict.Count; }
    }
    public long LongLength {
      get { return dict.Count; }
    }
    public bool Equals(Map<U, V> other) {
      foreach (U u in dict.Keys) {
        V v1, v2;
        if (!dict.TryGetValue(u, out v1)) {
          return false; // this shouldn't happen
        }
        if (!other.dict.TryGetValue(u, out v2)) {
          return false; // other dictionary does not contain this element
        }
        if (!v1.Equals(v2)) {
          return false;
        }
      }
      foreach (U u in other.dict.Keys) {
        if (!dict.ContainsKey(u)) {
          return false; // this shouldn't happen
        }
      }
      return true;
    }
    public override bool Equals(object other) {
      return other is Map<U, V> && Equals((Map<U, V>)other);
    }
    public override int GetHashCode() {
      var hashCode = 1;
      foreach (var kv in dict) {
        var key = kv.Key.GetHashCode();
        key = (key << 3) | (key >> 29) ^ kv.Value.GetHashCode();
        hashCode = hashCode * (key + 3);
      }
      return hashCode;
    }
    public override string ToString() {
      var s = "map[";
      var sep = "";
      foreach (var kv in dict) {
        s += sep + kv.Key.ToString() + " := " + kv.Value.ToString();
        sep = ", ";
      }
      return s + "]";
    }
    public bool IsDisjointFrom(Map<U, V> other) {
      foreach (U u in dict.Keys) {
        if (other.dict.ContainsKey(u))
          return false;
      }
      foreach (U u in other.dict.Keys) {
        if (dict.ContainsKey(u))
          return false;
      }
      return true;
    }
    public bool Contains(U u) {
      return dict.ContainsKey(u);
    }
    public V Select(U index) {
      return dict[index];
    }
    public Map<U, V> Update(U index, V val) {
      return new Map<U, V>(dict.SetItem(index, val));
    }
    public IEnumerable<U> Domain {
      get {
        return dict.Keys;
      }
    }
  }
#else // !def DAFNY_USE_SYSTEM_COLLECTIONS_IMMUTABLE
  public class Set<T>
  {
    HashSet<T> set;
    Set(HashSet<T> s) {
      this.set = s;
    }
    public static Set<T> Empty {
      get {
        return new Set<T>(new HashSet<T>());
      }
    }
    public static Set<T> FromElements(params T[] values) {
      var s = new HashSet<T>();
      foreach (T t in values)
        s.Add(t);
      return new Set<T>(s);
    }
    public static Set<T> FromCollection(ICollection<T> values) {
      HashSet<T> s = new HashSet<T>();
      foreach (T t in values)
        s.Add(t);
      return new Set<T>(s);
    }
    public int Length {
      get { return this.set.Count; }
    }
    public long LongLength {
      get { return this.set.Count; }
    }
    public IEnumerable<T> Elements {
      get {
        return this.set;
      }
    }
    /// <summary>
    /// This is an inefficient iterator for producing all subsets of "this".  Each set returned is the same
    /// Set<T> object (but this Set<T> object is fresh; in particular, it is not "this").
    /// </summary>
    public IEnumerable<Set<T>> AllSubsets {
      get {
        // Start by putting all set elements into a list
        var elmts = new List<T>();
        elmts.AddRange(this.set);
        var n = elmts.Count;
        var which = new bool[n];
        var s = new Set<T>(new HashSet<T>());
        while (true) {
          yield return s;
          // "add 1" to "which", as if doing a carry chain.  For every digit changed, change the membership of the corresponding element in "s".
          int i = 0;
          for (; i < n && which[i]; i++) {
            which[i] = false;
            s.set.Remove(elmts[i]);
          }
          if (i == n) {
            // we have cycled through all the subsets
            break;
          }
          which[i] = true;
          s.set.Add(elmts[i]);
        }
      }
    }
    public bool Equals(Set<T> other) {
      return this.set.Count == other.set.Count && IsSubsetOf(other);
    }
    public override bool Equals(object other) {
      return other is Set<T> && Equals((Set<T>)other);
    }
    public override int GetHashCode() {
      var hashCode = 1;
      foreach (var t in this.set) {
        hashCode = hashCode * (t.GetHashCode()+3);
      }
      return hashCode;
    }
    public override string ToString() {
      var s = "{";
      var sep = "";
      foreach (var t in this.set) {
        s += sep + t.ToString();
        sep = ", ";
      }
      return s + "}";
    }
    public bool IsProperSubsetOf(Set<T> other) {
      return this.set.Count < other.set.Count && IsSubsetOf(other);
    }
    public bool IsSubsetOf(Set<T> other) {
      if (other.set.Count < this.set.Count)
        return false;
      foreach (T t in this.set) {
        if (!other.set.Contains(t))
          return false;
      }
      return true;
    }
    public bool IsSupersetOf(Set<T> other) {
      return other.IsSubsetOf(this);
    }
    public bool IsProperSupersetOf(Set<T> other) {
      return other.IsProperSubsetOf(this);
    }
    public bool IsDisjointFrom(Set<T> other) {
      HashSet<T> a, b;
      if (this.set.Count < other.set.Count) {
        a = this.set; b = other.set;
      } else {
        a = other.set; b = this.set;
      }
      foreach (T t in a) {
        if (b.Contains(t))
          return false;
      }
      return true;
    }
    public bool Contains(T t) {
      return this.set.Contains(t);
    }
    public Set<T> Union(Set<T> other) {
      if (this.set.Count == 0)
        return other;
      else if (other.set.Count == 0)
        return this;
      HashSet<T> a, b;
      if (this.set.Count < other.set.Count) {
        a = this.set; b = other.set;
      } else {
        a = other.set; b = this.set;
      }
      var r = new HashSet<T>();
      foreach (T t in b)
        r.Add(t);
      foreach (T t in a)
        r.Add(t);
      return new Set<T>(r);
    }
    public Set<T> Intersect(Set<T> other) {
      if (this.set.Count == 0)
        return this;
      else if (other.set.Count == 0)
        return other;
      HashSet<T> a, b;
      if (this.set.Count < other.set.Count) {
        a = this.set; b = other.set;
      } else {
        a = other.set; b = this.set;
      }
      var r = new HashSet<T>();
      foreach (T t in a) {
        if (b.Contains(t))
          r.Add(t);
      }
      return new Set<T>(r);
    }
    public Set<T> Difference(Set<T> other) {
      if (this.set.Count == 0)
        return this;
      else if (other.set.Count == 0)
        return this;
      var r = new HashSet<T>();
      foreach (T t in this.set) {
        if (!other.set.Contains(t))
          r.Add(t);
      }
      return new Set<T>(r);
    }
  }
  public class MultiSet<T>
  {
    Dictionary<T, int> dict;
    MultiSet(Dictionary<T, int> d) {
      dict = d;
    }
    public static MultiSet<T> Empty {
      get {
        return new MultiSet<T>(new Dictionary<T, int>(0));
      }
    }
    public static MultiSet<T> FromElements(params T[] values) {
      Dictionary<T, int> d = new Dictionary<T, int>(values.Length);
      foreach (T t in values) {
        var i = 0;
        if (!d.TryGetValue(t, out i)) {
          i = 0;
        }
        d[t] = i + 1;
      }
      return new MultiSet<T>(d);
    }
    public static MultiSet<T> FromCollection(ICollection<T> values) {
      Dictionary<T, int> d = new Dictionary<T, int>();
      foreach (T t in values) {
        var i = 0;
        if (!d.TryGetValue(t, out i)) {
          i = 0;
        }
        d[t] = i + 1;
      }
      return new MultiSet<T>(d);
    }
    public static MultiSet<T> FromSeq(Sequence<T> values) {
      Dictionary<T, int> d = new Dictionary<T, int>();
      foreach (T t in values.Elements) {
        var i = 0;
        if (!d.TryGetValue(t, out i)) {
          i = 0;
        }
        d[t] = i + 1;
      }
      return new MultiSet<T>(d);
    }
    public static MultiSet<T> FromSet(Set<T> values) {
      Dictionary<T, int> d = new Dictionary<T, int>();
      foreach (T t in values.Elements) {
        d[t] = 1;
      }
      return new MultiSet<T>(d);
    }

    public bool Equals(MultiSet<T> other) {
      return other.IsSubsetOf(this) && this.IsSubsetOf(other);
    }
    public override bool Equals(object other) {
      return other is MultiSet<T> && Equals((MultiSet<T>)other);
    }
    public override int GetHashCode() {
      var hashCode = 1;
      foreach (var kv in dict) {
        var key = kv.Key.GetHashCode();
        key = (key << 3) | (key >> 29) ^ kv.Value.GetHashCode();
        hashCode = hashCode * (key + 3);
      }
      return hashCode;
    }
    public override string ToString() {
      var s = "multiset{";
      var sep = "";
      foreach (var kv in dict) {
        var t = kv.Key.ToString();
        for (int i = 0; i < kv.Value; i++) {
          s += sep + t.ToString();
          sep = ", ";
        }
      }
      return s + "}";
    }
    public bool IsProperSubsetOf(MultiSet<T> other) {
      return !Equals(other) && IsSubsetOf(other);
    }
    public bool IsSubsetOf(MultiSet<T> other) {
      foreach (T t in dict.Keys) {
        if (!other.dict.ContainsKey(t) || other.dict[t] < dict[t])
          return false;
      }
      return true;
    }
    public bool IsSupersetOf(MultiSet<T> other) {
      return other.IsSubsetOf(this);
    }
    public bool IsProperSupersetOf(MultiSet<T> other) {
      return other.IsProperSubsetOf(this);
    }
    public bool IsDisjointFrom(MultiSet<T> other) {
      foreach (T t in dict.Keys) {
        if (other.dict.ContainsKey(t))
          return false;
      }
      foreach (T t in other.dict.Keys) {
        if (dict.ContainsKey(t))
          return false;
      }
      return true;
    }
    public bool Contains(T t) {
      return dict.ContainsKey(t);
    }
    public MultiSet<T> Union(MultiSet<T> other) {
      if (dict.Count == 0)
        return other;
      else if (other.dict.Count == 0)
        return this;
      var r = new Dictionary<T, int>();
      foreach (T t in dict.Keys) {
        var i = 0;
        if (!r.TryGetValue(t, out i)) {
          i = 0;
        }
        r[t] = i + dict[t];
      }
      foreach (T t in other.dict.Keys) {
        var i = 0;
        if (!r.TryGetValue(t, out i)) {
          i = 0;
        }
        r[t] = i + other.dict[t];
      }
      return new MultiSet<T>(r);
    }
    public MultiSet<T> Intersect(MultiSet<T> other) {
      if (dict.Count == 0)
        return this;
      else if (other.dict.Count == 0)
        return other;
      var r = new Dictionary<T, int>();
      foreach (T t in dict.Keys) {
        if (other.dict.ContainsKey(t)) {
          r.Add(t, other.dict[t] < dict[t] ? other.dict[t] : dict[t]);
        }
      }
      return new MultiSet<T>(r);
    }
    public MultiSet<T> Difference(MultiSet<T> other) { // \result == this - other
      if (dict.Count == 0)
        return this;
      else if (other.dict.Count == 0)
        return this;
      var r = new Dictionary<T, int>();
      foreach (T t in dict.Keys) {
        if (!other.dict.ContainsKey(t)) {
          r.Add(t, dict[t]);
        } else if (other.dict[t] < dict[t]) {
          r.Add(t, dict[t] - other.dict[t]);
        }
      }
      return new MultiSet<T>(r);
    }
    public IEnumerable<T> Elements {
      get {
        List<T> l = new List<T>();
        foreach (T t in dict.Keys) {
          int n;
          dict.TryGetValue(t, out n);
          for (int i = 0; i < n; i ++) {
            l.Add(t);
          }
        }
        return l;
      }
    }
  }

  public class Map<U, V>
  {
    Dictionary<U, V> dict;
    Map(Dictionary<U, V> d) {
      dict = d;
    }
    public static Map<U, V> Empty {
      get {
        return new Map<U, V>(new Dictionary<U,V>());
      }
    }
    public static Map<U, V> FromElements(params Pair<U, V>[] values) {
      Dictionary<U, V> d = new Dictionary<U, V>(values.Length);
      foreach (Pair<U, V> p in values) {
        d[p.Car] = p.Cdr;
      }
      return new Map<U, V>(d);
    }
    public static Map<U, V> FromCollection(List<Pair<U, V>> values) {
      Dictionary<U, V> d = new Dictionary<U, V>(values.Count);
      foreach (Pair<U, V> p in values) {
        d[p.Car] = p.Cdr;
      }
      return new Map<U, V>(d);
    }
    public int Length {
      get { return dict.Count; }
    }
    public long LongLength {
      get { return dict.Count; }
    }
    public bool Equals(Map<U, V> other) {
      foreach (U u in dict.Keys) {
        V v1, v2;
        if (!dict.TryGetValue(u, out v1)) {
          return false; // this shouldn't happen
        }
        if (!other.dict.TryGetValue(u, out v2)) {
          return false; // other dictionary does not contain this element
        }
        if (!v1.Equals(v2)) {
          return false;
        }
      }
      foreach (U u in other.dict.Keys) {
        if (!dict.ContainsKey(u)) {
          return false; // this shouldn't happen
        }
      }
      return true;
    }
    public override bool Equals(object other) {
      return other is Map<U, V> && Equals((Map<U, V>)other);
    }
    public override int GetHashCode() {
      var hashCode = 1;
      foreach (var kv in dict) {
        var key = kv.Key.GetHashCode();
        key = (key << 3) | (key >> 29) ^ kv.Value.GetHashCode();
        hashCode = hashCode * (key + 3);
      }
      return hashCode;
    }
    public override string ToString() {
      var s = "map[";
      var sep = "";
      foreach (var kv in dict) {
        s += sep + kv.Key.ToString() + " := " + kv.Value.ToString();
        sep = ", ";
      }
      return s + "]";
    }
    public bool IsDisjointFrom(Map<U, V> other) {
      foreach (U u in dict.Keys) {
        if (other.dict.ContainsKey(u))
          return false;
      }
      foreach (U u in other.dict.Keys) {
        if (dict.ContainsKey(u))
          return false;
      }
      return true;
    }
    public bool Contains(U u) {
      return dict.ContainsKey(u);
    }
    public V Select(U index) {
      return dict[index];
    }
    public Map<U, V> Update(U index, V val) {
      Dictionary<U, V> d = new Dictionary<U, V>(dict);
      d[index] = val;
      return new Map<U, V>(d);
    }
    public IEnumerable<U> Domain {
      get {
        return dict.Keys;
      }
    }
  }
#endif
  public class Sequence<T>
  {
    T[] elmts;
    public Sequence(T[] ee) {
      elmts = ee;
    }
    public static Sequence<T> Empty {
      get {
        return new Sequence<T>(new T[0]);
      }
    }
    public static Sequence<T> FromElements(params T[] values) {
      return new Sequence<T>(values);
    }
    public static Sequence<char> FromString(string s) {
      return new Sequence<char>(s.ToCharArray());
    }
    public int Length {
      get { return elmts.Length; }
    }
    public long LongLength {
      get { return elmts.LongLength; }
    }
    public T[] Elements {
      get {
        return elmts;
      }
    }
    public IEnumerable<T> UniqueElements {
      get {
        var st = Set<T>.FromElements(elmts);
        return st.Elements;
      }
    }
    public T Select(ulong index) {
      return elmts[index];
    }
    public T Select(long index) {
      return elmts[index];
    }
    public T Select(uint index) {
      return elmts[index];
    }
    public T Select(int index) {
      return elmts[index];
    }
    public T Select(BigInteger index) {
      return elmts[(int)index];
    }
    public Sequence<T> Update(long index, T t) {
      T[] a = (T[])elmts.Clone();
      a[index] = t;
      return new Sequence<T>(a);
    }
    public Sequence<T> Update(ulong index, T t) {
      return Update((long)index, t);
    }
    public Sequence<T> Update(BigInteger index, T t) {
      return Update((long)index, t);
    }
    public bool Equals(Sequence<T> other) {
      int n = elmts.Length;
      return n == other.elmts.Length && EqualUntil(other, n);
    }
    public override bool Equals(object other) {
      return other is Sequence<T> && Equals((Sequence<T>)other);
    }
    public override int GetHashCode() {
      if (elmts == null || elmts.Length == 0)
        return 0;
      var hashCode = 0;
      for (var i = 0; i < elmts.Length; i++) {
        hashCode = (hashCode << 3) | (hashCode >> 29) ^ elmts[i].GetHashCode();
      }
      return hashCode;
    }
    public override string ToString() {
      if (elmts is char[]) {
        var s = "";
        foreach (var t in elmts) {
          s += t.ToString();
        }
        return s;
      } else {
        var s = "[";
        var sep = "";
        foreach (var t in elmts) {
          s += sep + t.ToString();
          sep = ", ";
        }
        return s + "]";
      }
    }
    bool EqualUntil(Sequence<T> other, int n) {
      for (int i = 0; i < n; i++) {
        if (!elmts[i].Equals(other.elmts[i]))
          return false;
      }
      return true;
    }
    public bool IsProperPrefixOf(Sequence<T> other) {
      int n = elmts.Length;
      return n < other.elmts.Length && EqualUntil(other, n);
    }
    public bool IsPrefixOf(Sequence<T> other) {
      int n = elmts.Length;
      return n <= other.elmts.Length && EqualUntil(other, n);
    }
    public Sequence<T> Concat(Sequence<T> other) {
      if (elmts.Length == 0)
        return other;
      else if (other.elmts.Length == 0)
        return this;
      T[] a = new T[elmts.Length + other.elmts.Length];
      System.Array.Copy(elmts, 0, a, 0, elmts.Length);
      System.Array.Copy(other.elmts, 0, a, elmts.Length, other.elmts.Length);
      return new Sequence<T>(a);
    }
    public bool Contains(T t) {
      int n = elmts.Length;
      for (int i = 0; i < n; i++) {
        if (t.Equals(elmts[i]))
          return true;
      }
      return false;
    }
    public Sequence<T> Take(long m) {
      if (elmts.LongLength == m)
        return this;
      T[] a = new T[m];
      System.Array.Copy(elmts, a, m);
      return new Sequence<T>(a);
    }
    public Sequence<T> Take(ulong n) {
      return Take((long)n);
    }
    public Sequence<T> Take(BigInteger n) {
      return Take((long)n);
    }
    public Sequence<T> Drop(long m) {
      if (m == 0)
        return this;
      T[] a = new T[elmts.Length - m];
      System.Array.Copy(elmts, m, a, 0, elmts.Length - m);
      return new Sequence<T>(a);
    }
    public Sequence<T> Drop(ulong n) {
      return Drop((long)n);
    }
    public Sequence<T> Drop(BigInteger n) {
      if (n.IsZero)
        return this;
      return Drop((long)n);
    }
  }
  public struct Pair<A, B>
  {
    public readonly A Car;
    public readonly B Cdr;
    public Pair(A a, B b) {
      this.Car = a;
      this.Cdr = b;
    }
  }
  public partial class Helpers {
    public static System.Predicate<BigInteger> PredicateConverter_byte(System.Predicate<byte> pred) {
      return x => pred((byte)x);
    }
    public static System.Predicate<BigInteger> PredicateConverter_sbyte(System.Predicate<sbyte> pred) {
      return x => pred((sbyte)x);
    }
    public static System.Predicate<BigInteger> PredicateConverter_ushort(System.Predicate<ushort> pred) {
      return x => pred((ushort)x);
    }
    public static System.Predicate<BigInteger> PredicateConverter_short(System.Predicate<short> pred) {
      return x => pred((short)x);
    }
    public static System.Predicate<BigInteger> PredicateConverter_uint(System.Predicate<uint> pred) {
      return x => pred((uint)x);
    }
    public static System.Predicate<BigInteger> PredicateConverter_int(System.Predicate<int> pred) {
      return x => pred((int)x);
    }
    public static System.Predicate<BigInteger> PredicateConverter_ulong(System.Predicate<ulong> pred) {
      return x => pred((ulong)x);
    }
    public static System.Predicate<BigInteger> PredicateConverter_long(System.Predicate<long> pred) {
      return x => pred((long)x);
    }
    // Computing forall/exists quantifiers
    public static bool QuantBool(bool frall, System.Predicate<bool> pred) {
      if (frall) {
        return pred(false) && pred(true);
      } else {
        return pred(false) || pred(true);
      }
    }
    public static bool QuantChar(bool frall, System.Predicate<char> pred) {
      for (int i = 0; i < 0x10000; i++) {
        if (pred((char)i) != frall) { return !frall; }
      }
      return frall;
    }
    public static bool QuantInt(BigInteger lo, BigInteger hi, bool frall, System.Predicate<BigInteger> pred) {
      for (BigInteger i = lo; i < hi; i++) {
        if (pred(i) != frall) { return !frall; }
      }
      return frall;
    }
    public static bool QuantSet<U>(Dafny.Set<U> set, bool frall, System.Predicate<U> pred) {
      foreach (var u in set.Elements) {
        if (pred(u) != frall) { return !frall; }
      }
      return frall;
    }
    public static bool QuantMap<U,V>(Dafny.Map<U,V> map, bool frall, System.Predicate<U> pred) {
      foreach (var u in map.Domain) {
        if (pred(u) != frall) { return !frall; }
      }
      return frall;
    }
    public static bool QuantSeq<U>(Dafny.Sequence<U> seq, bool frall, System.Predicate<U> pred) {
      foreach (var u in seq.Elements) {
        if (pred(u) != frall) { return !frall; }
      }
      return frall;
    }
    public static bool QuantDatatype<U>(IEnumerable<U> set, bool frall, System.Predicate<U> pred) {
      foreach (var u in set) {
        if (pred(u) != frall) { return !frall; }
      }
      return frall;
    }
    // Enumerating other collections
    public delegate Dafny.Set<T> ComprehensionDelegate<T>();
    public delegate Dafny.Map<U, V> MapComprehensionDelegate<U, V>();
    public static IEnumerable<bool> AllBooleans {
      get {
        yield return false;
        yield return true;
      }
    }
    public static IEnumerable<char> AllChars {
      get {
        for (int i = 0; i < 0x10000; i++) {
          yield return (char)i;
        }
      }
    }
    public static IEnumerable<BigInteger> AllIntegers {
      get {
        yield return new BigInteger(0);
        for (var j = new BigInteger(1);; j++) {
          yield return j;
          yield return -j;
        }
      }
    }
    public static IEnumerable<BigInteger> IntegerRange(Nullable<BigInteger> lo, Nullable<BigInteger> hi) {
      if (lo == null) {
        for (var j = (BigInteger)hi; true; ) {
          j--;
          yield return j;
        }
      } else if (hi == null) {
        for (var j = (BigInteger)lo; true; j++) {
          yield return j;
        }
      } else {
        for (var j = (BigInteger)lo; j < hi; j++) {
          yield return j;
        }
      }
    }
    // pre: b != 0
    // post: result == a/b, as defined by Euclidean Division (http://en.wikipedia.org/wiki/Modulo_operation)
    public static sbyte EuclideanDivision_sbyte(sbyte a, sbyte b) {
      return (sbyte)EuclideanDivision_int(a, b);
    }
    public static short EuclideanDivision_short(short a, short b) {
      return (short)EuclideanDivision_int(a, b);
    }
    public static int EuclideanDivision_int(int a, int b) {
      if (0 <= a) {
        if (0 <= b) {
          // +a +b: a/b
          return (int)(((uint)(a)) / ((uint)(b)));
        } else {
          // +a -b: -(a/(-b))
          return -((int)(((uint)(a)) / ((uint)(unchecked(-b)))));
        }
      } else {
        if (0 <= b) {
          // -a +b: -((-a-1)/b) - 1
          return -((int)(((uint)(-(a + 1))) / ((uint)(b)))) - 1;
        } else {
          // -a -b: ((-a-1)/(-b)) + 1
          return ((int)(((uint)(-(a + 1))) / ((uint)(unchecked(-b))))) + 1;
        }
      }
    }
    public static long EuclideanDivision_long(long a, long b) {
      if (0 <= a) {
        if (0 <= b) {
          // +a +b: a/b
          return (long)(((ulong)(a)) / ((ulong)(b)));
        } else {
          // +a -b: -(a/(-b))
          return -((long)(((ulong)(a)) / ((ulong)(unchecked(-b)))));
        }
      } else {
        if (0 <= b) {
          // -a +b: -((-a-1)/b) - 1
          return -((long)(((ulong)(-(a + 1))) / ((ulong)(b)))) - 1;
        } else {
          // -a -b: ((-a-1)/(-b)) + 1
          return ((long)(((ulong)(-(a + 1))) / ((ulong)(unchecked(-b))))) + 1;
        }
      }
    }
    public static BigInteger EuclideanDivision(BigInteger a, BigInteger b) {
      if (0 <= a.Sign) {
        if (0 <= b.Sign) {
          // +a +b: a/b
          return BigInteger.Divide(a, b);
        } else {
          // +a -b: -(a/(-b))
          return BigInteger.Negate(BigInteger.Divide(a, BigInteger.Negate(b)));
        }
      } else {
        if (0 <= b.Sign) {
          // -a +b: -((-a-1)/b) - 1
          return BigInteger.Negate(BigInteger.Divide(BigInteger.Negate(a) - 1, b)) - 1;
        } else {
          // -a -b: ((-a-1)/(-b)) + 1
          return BigInteger.Divide(BigInteger.Negate(a) - 1, BigInteger.Negate(b)) + 1;
        }
      }
    }
    // pre: b != 0
    // post: result == a%b, as defined by Euclidean Division (http://en.wikipedia.org/wiki/Modulo_operation)
    public static sbyte EuclideanModulus_sbyte(sbyte a, sbyte b) {
      return (sbyte)EuclideanModulus_int(a, b);
    }
    public static short EuclideanModulus_short(short a, short b) {
      return (short)EuclideanModulus_int(a, b);
    }
    public static int EuclideanModulus_int(int a, int b) {
      uint bp = (0 <= b) ? (uint)b : (uint)(unchecked(-b));
      if (0 <= a) {
        // +a: a % b'
        return (int)(((uint)a) % bp);
      } else {
        // c = ((-a) % b')
        // -a: b' - c if c > 0
        // -a: 0 if c == 0
        uint c = ((uint)(unchecked(-a))) % bp;
        return (int)(c == 0 ? c : bp - c);
      }
    }
    public static long EuclideanModulus_long(long a, long b) {
      ulong bp = (0 <= b) ? (ulong)b : (ulong)(unchecked(-b));
      if (0 <= a) {
        // +a: a % b'
        return (long)(((ulong)a) % bp);
      } else {
        // c = ((-a) % b')
        // -a: b' - c if c > 0
        // -a: 0 if c == 0
        ulong c = ((ulong)(unchecked(-a))) % bp;
        return (long)(c == 0 ? c : bp - c);
      }
    }
    public static BigInteger EuclideanModulus(BigInteger a, BigInteger b) {
      var bp = BigInteger.Abs(b);
      if (0 <= a.Sign) {
        // +a: a % b'
        return BigInteger.Remainder(a, bp);
      } else {
        // c = ((-a) % b')
        // -a: b' - c if c > 0
        // -a: 0 if c == 0
        var c = BigInteger.Remainder(BigInteger.Negate(a), bp);
        return c.IsZero ? c : BigInteger.Subtract(bp, c);
      }
    }
    public static Sequence<T> SeqFromArray<T>(T[] array) {
      return new Sequence<T>((T[])array.Clone());
    }
    // In .NET version 4.5, it it possible to mark a method with "AggressiveInlining", which says to inline the
    // method if possible.  Method "ExpressionSequence" would be a good candidate for it:
    // [System.Runtime.CompilerServices.MethodImpl(System.Runtime.CompilerServices.MethodImplOptions.AggressiveInlining)]
    public static U ExpressionSequence<T, U>(T t, U u)
    {
      return u;
    }

    public static U Let<T, U>(T t, Func<T,U> f) {
      return f(t);
    }

    public delegate Result Function<Input,Result>(Input input);

    public static A Id<A>(A a) {
      return a;
    }
  }

  public struct BigRational
  {
    public static readonly BigRational ZERO = new BigRational(0);

    BigInteger num, den;  // invariant 1 <= den
    public override string ToString() {
      return string.Format("({0}.0 / {1}.0)", num, den);
    }
    public BigRational(int n) {
      num = new BigInteger(n);
      den = BigInteger.One;
    }
    public BigRational(BigInteger n, BigInteger d) {
      // requires 1 <= d
      num = n;
      den = d;
    }
    public BigInteger ToBigInteger() {
      if (0 <= num) {
        return num / den;
      } else {
        return (num - den + 1) / den;
      }
    }
    /// <summary>
    /// Returns values such that aa/dd == a and bb/dd == b.
    /// </summary>
    private static void Normalize(BigRational a, BigRational b, out BigInteger aa, out BigInteger bb, out BigInteger dd) {
      var gcd = BigInteger.GreatestCommonDivisor(a.den, b.den);
      var xx = a.den / gcd;
      var yy = b.den / gcd;
      // We now have a == a.num / (xx * gcd) and b == b.num / (yy * gcd).
      aa = a.num * yy;
      bb = b.num * xx;
      dd = a.den * yy;
    }
    public int CompareTo(BigRational that) {
      // simple things first
      int asign = this.num.Sign;
      int bsign = that.num.Sign;
      if (asign < 0 && 0 <= bsign) {
        return -1;
      } else if (asign <= 0 && 0 < bsign) {
        return -1;
      } else if (bsign < 0 && 0 <= asign) {
        return 1;
      } else if (bsign <= 0 && 0 < asign) {
        return 1;
      }
      BigInteger aa, bb, dd;
      Normalize(this, that, out aa, out bb, out dd);
      return aa.CompareTo(bb);
    }
    public override int GetHashCode() {
      return num.GetHashCode() + 29 * den.GetHashCode();
    }
    public override bool Equals(object obj) {
      if (obj is BigRational) {
        return this == (BigRational)obj;
      } else {
        return false;
      }
    }
    public static bool operator ==(BigRational a, BigRational b) {
      return a.CompareTo(b) == 0;
    }
    public static bool operator !=(BigRational a, BigRational b) {
      return a.CompareTo(b) != 0;
    }
    public static bool operator >(BigRational a, BigRational b) {
      return 0 < a.CompareTo(b);
    }
    public static bool operator >=(BigRational a, BigRational b) {
      return 0 <= a.CompareTo(b);
    }
    public static bool operator <(BigRational a, BigRational b) {
      return a.CompareTo(b) < 0;
    }
    public static bool operator <=(BigRational a, BigRational b) {
      return a.CompareTo(b) <= 0;
    }
    public static BigRational operator +(BigRational a, BigRational b) {
      BigInteger aa, bb, dd;
      Normalize(a, b, out aa, out bb, out dd);
      return new BigRational(aa + bb, dd);
    }
    public static BigRational operator -(BigRational a, BigRational b) {
      BigInteger aa, bb, dd;
      Normalize(a, b, out aa, out bb, out dd);
      return new BigRational(aa - bb, dd);
    }
    public static BigRational operator -(BigRational a) {
      return new BigRational(-a.num, a.den);
    }
    public static BigRational operator *(BigRational a, BigRational b) {
      return new BigRational(a.num * b.num, a.den * b.den);
    }
    public static BigRational operator /(BigRational a, BigRational b) {
      // Compute the reciprocal of b
      BigRational bReciprocal;
      if (0 < b.num) {
        bReciprocal = new BigRational(b.den, b.num);
      } else {
        // this is the case b.num < 0
        bReciprocal = new BigRational(-b.den, -b.num);
      }
      return a * bReciprocal;
    }
  }
}
namespace Dafny {
  public partial class Helpers {
      public static T[] InitNewArray1<T>(BigInteger size0) {
        int s0 = (int)size0;
        T[] a = new T[s0];
        BigInteger[] b = a as BigInteger[];
        if (b != null) {
          BigInteger z = new BigInteger(0);
          for (int i0 = 0; i0 < s0; i0++)
            b[i0] = z;
        }
        return a;
      }
  }
}
namespace @_System {



  public abstract class Base___tuple_h2<@T0,@T1> { }
  public class __tuple_h2____hMake2<@T0,@T1> : Base___tuple_h2<@T0,@T1> {
    public readonly @T0 @_0;
    public readonly @T1 @_1;
    public __tuple_h2____hMake2(@T0 @_0, @T1 @_1) {
      this.@_0 = @_0;
      this.@_1 = @_1;
    }
    public override bool Equals(object other) {
      var oth = other as _System.@__tuple_h2____hMake2<@T0,@T1>;
      return oth != null && this.@_0.Equals(oth.@_0) && this.@_1.Equals(oth.@_1);
    }
    public override int GetHashCode() {
      ulong hash = 5381;
      hash = ((hash << 5) + hash) + 0;
      hash = ((hash << 5) + hash) + ((ulong)this.@_0.GetHashCode());
      hash = ((hash << 5) + hash) + ((ulong)this.@_1.GetHashCode());
      return (int) hash;
    }
    public override string ToString() {
      string s = "";
      s += "(";
      s += @_0.ToString();
      s += ", ";
      s += @_1.ToString();
      s += ")";
      return s;
    }
  }
  public struct @__tuple_h2<@T0,@T1> {
    Base___tuple_h2<@T0,@T1> _d;
    public Base___tuple_h2<@T0,@T1> _D {
      get {
        if (_d == null) {
          _d = Default;
        }
        return _d;
      }
    }
    public @__tuple_h2(Base___tuple_h2<@T0,@T1> d) { this._d = d; }
    static Base___tuple_h2<@T0,@T1> theDefault;
    public static Base___tuple_h2<@T0,@T1> Default {
      get {
        if (theDefault == null) {
          theDefault = new _System.@__tuple_h2____hMake2<@T0,@T1>(default(@T0), default(@T1));
        }
        return theDefault;
      }
    }
    public override bool Equals(object other) {
      return other is @__tuple_h2<@T0,@T1> && _D.Equals(((@__tuple_h2<@T0,@T1>)other)._D);
    }
    public override int GetHashCode() { return _D.GetHashCode(); }
    public override string ToString() { return _D.ToString(); }
    public bool is____hMake2 { get { return _D is __tuple_h2____hMake2<@T0,@T1>; } }
    public @T0 dtor__0 { get { return ((__tuple_h2____hMake2<@T0,@T1>)_D).@_0; } }
    public @T1 dtor__1 { get { return ((__tuple_h2____hMake2<@T0,@T1>)_D).@_1; } }
  }
} // end of namespace _System

public abstract class Base_Disk { }
public class Disk_White : Base_Disk {
  public Disk_White() {
  }
  public override bool Equals(object other) {
    var oth = other as Disk_White;
    return oth != null;
  }
  public override int GetHashCode() {
    ulong hash = 5381;
    hash = ((hash << 5) + hash) + 0;
    return (int) hash;
  }
  public override string ToString() {
    string s = "Disk.White";
    return s;
  }
}
public class Disk_Black : Base_Disk {
  public Disk_Black() {
  }
  public override bool Equals(object other) {
    var oth = other as Disk_Black;
    return oth != null;
  }
  public override int GetHashCode() {
    ulong hash = 5381;
    hash = ((hash << 5) + hash) + 0;
    return (int) hash;
  }
  public override string ToString() {
    string s = "Disk.Black";
    return s;
  }
}
public struct @Disk {
  Base_Disk _d;
  public Base_Disk _D {
    get {
      if (_d == null) {
        _d = Default;
      }
      return _d;
    }
  }
  public @Disk(Base_Disk d) { this._d = d; }
  static Base_Disk theDefault;
  public static Base_Disk Default {
    get {
      if (theDefault == null) {
        theDefault = new Disk_White();
      }
      return theDefault;
    }
  }
  public override bool Equals(object other) {
    return other is @Disk && _D.Equals(((@Disk)other)._D);
  }
  public override int GetHashCode() { return _D.GetHashCode(); }
  public override string ToString() { return _D.ToString(); }
  public bool is_White { get { return _D is Disk_White; } }
  public bool is_Black { get { return _D is Disk_Black; } }
  public static System.Collections.Generic.IEnumerable<@Disk> AllSingletonConstructors {
    get {
      yield return new @Disk(new Disk_White());
      yield return new @Disk(new Disk_Black());
      yield break;
    }
  }
}



public abstract class Base_Direction { }
public class Direction_Up : Base_Direction {
  public Direction_Up() {
  }
  public override bool Equals(object other) {
    var oth = other as Direction_Up;
    return oth != null;
  }
  public override int GetHashCode() {
    ulong hash = 5381;
    hash = ((hash << 5) + hash) + 0;
    return (int) hash;
  }
  public override string ToString() {
    string s = "Direction.Up";
    return s;
  }
}
public class Direction_UpRight : Base_Direction {
  public Direction_UpRight() {
  }
  public override bool Equals(object other) {
    var oth = other as Direction_UpRight;
    return oth != null;
  }
  public override int GetHashCode() {
    ulong hash = 5381;
    hash = ((hash << 5) + hash) + 0;
    return (int) hash;
  }
  public override string ToString() {
    string s = "Direction.UpRight";
    return s;
  }
}
public class Direction_Right : Base_Direction {
  public Direction_Right() {
  }
  public override bool Equals(object other) {
    var oth = other as Direction_Right;
    return oth != null;
  }
  public override int GetHashCode() {
    ulong hash = 5381;
    hash = ((hash << 5) + hash) + 0;
    return (int) hash;
  }
  public override string ToString() {
    string s = "Direction.Right";
    return s;
  }
}
public class Direction_DownRight : Base_Direction {
  public Direction_DownRight() {
  }
  public override bool Equals(object other) {
    var oth = other as Direction_DownRight;
    return oth != null;
  }
  public override int GetHashCode() {
    ulong hash = 5381;
    hash = ((hash << 5) + hash) + 0;
    return (int) hash;
  }
  public override string ToString() {
    string s = "Direction.DownRight";
    return s;
  }
}
public class Direction_Down : Base_Direction {
  public Direction_Down() {
  }
  public override bool Equals(object other) {
    var oth = other as Direction_Down;
    return oth != null;
  }
  public override int GetHashCode() {
    ulong hash = 5381;
    hash = ((hash << 5) + hash) + 0;
    return (int) hash;
  }
  public override string ToString() {
    string s = "Direction.Down";
    return s;
  }
}
public class Direction_DownLeft : Base_Direction {
  public Direction_DownLeft() {
  }
  public override bool Equals(object other) {
    var oth = other as Direction_DownLeft;
    return oth != null;
  }
  public override int GetHashCode() {
    ulong hash = 5381;
    hash = ((hash << 5) + hash) + 0;
    return (int) hash;
  }
  public override string ToString() {
    string s = "Direction.DownLeft";
    return s;
  }
}
public class Direction_Left : Base_Direction {
  public Direction_Left() {
  }
  public override bool Equals(object other) {
    var oth = other as Direction_Left;
    return oth != null;
  }
  public override int GetHashCode() {
    ulong hash = 5381;
    hash = ((hash << 5) + hash) + 0;
    return (int) hash;
  }
  public override string ToString() {
    string s = "Direction.Left";
    return s;
  }
}
public class Direction_UpLeft : Base_Direction {
  public Direction_UpLeft() {
  }
  public override bool Equals(object other) {
    var oth = other as Direction_UpLeft;
    return oth != null;
  }
  public override int GetHashCode() {
    ulong hash = 5381;
    hash = ((hash << 5) + hash) + 0;
    return (int) hash;
  }
  public override string ToString() {
    string s = "Direction.UpLeft";
    return s;
  }
}
public struct @Direction {
  Base_Direction _d;
  public Base_Direction _D {
    get {
      if (_d == null) {
        _d = Default;
      }
      return _d;
    }
  }
  public @Direction(Base_Direction d) { this._d = d; }
  static Base_Direction theDefault;
  public static Base_Direction Default {
    get {
      if (theDefault == null) {
        theDefault = new Direction_Up();
      }
      return theDefault;
    }
  }
  public override bool Equals(object other) {
    return other is @Direction && _D.Equals(((@Direction)other)._D);
  }
  public override int GetHashCode() { return _D.GetHashCode(); }
  public override string ToString() { return _D.ToString(); }
  public bool is_Up { get { return _D is Direction_Up; } }
  public bool is_UpRight { get { return _D is Direction_UpRight; } }
  public bool is_Right { get { return _D is Direction_Right; } }
  public bool is_DownRight { get { return _D is Direction_DownRight; } }
  public bool is_Down { get { return _D is Direction_Down; } }
  public bool is_DownLeft { get { return _D is Direction_DownLeft; } }
  public bool is_Left { get { return _D is Direction_Left; } }
  public bool is_UpLeft { get { return _D is Direction_UpLeft; } }
  public static System.Collections.Generic.IEnumerable<@Direction> AllSingletonConstructors {
    get {
      yield return new @Direction(new Direction_Up());
      yield return new @Direction(new Direction_UpRight());
      yield return new @Direction(new Direction_Right());
      yield return new @Direction(new Direction_DownRight());
      yield return new @Direction(new Direction_Down());
      yield return new @Direction(new Direction_DownLeft());
      yield return new @Direction(new Direction_Left());
      yield return new @Direction(new Direction_UpLeft());
      yield break;
    }
  }
}

public partial class @__default {
  public static void @Main()
  {
  TAIL_CALL_START: ;
  }
  public static void @PrintMoveDetails(Dafny.Map<@_System.@__tuple_h2<BigInteger,BigInteger>,@Disk> @board, @Disk @player, @_System.@__tuple_h2<BigInteger,BigInteger> @move)
  {
  TAIL_CALL_START: ;
    System.Console.Write(Dafny.Sequence<char>.FromString("\n"));
    System.Console.Write(@player);
    System.Console.Write(Dafny.Sequence<char>.FromString(" is placed on row "));
    System.Console.Write((@move).@dtor__0);
    System.Console.Write(Dafny.Sequence<char>.FromString(" and column "));
    System.Console.Write((@move).@dtor__1);
    Dafny.Set<@Direction> @_55690_reversibleDirections = Dafny.Set<@Direction>.Empty;
    Dafny.Set<@Direction> _out0;
    @__default.@FindAllLegalDirectionsFrom(@board, @player, @move, out _out0);
    @_55690_reversibleDirections = _out0;
    System.Console.Write(Dafny.Sequence<char>.FromString(" with reversible directions "));
    System.Console.Write(@_55690_reversibleDirections);
    Dafny.Set<@_System.@__tuple_h2<BigInteger,BigInteger>> @_55691_reversiblePositions = Dafny.Set<@_System.@__tuple_h2<BigInteger,BigInteger>>.Empty;
    Dafny.Set<@_System.@__tuple_h2<BigInteger,BigInteger>> _out1;
    @__default.@FindAllReversiblePositionsFrom(@board, @player, @move, out _out1);
    @_55691_reversiblePositions = _out1;
    System.Console.Write(Dafny.Sequence<char>.FromString(" and reversible positions "));
    System.Console.Write(@_55691_reversiblePositions);
  }
  public static void @PrintResults(BigInteger @blacks, BigInteger @whites)
  {
  TAIL_CALL_START: ;
    System.Console.Write(Dafny.Sequence<char>.FromString("\nGame Over.\nAnd the winner is... "));
    System.Console.Write(((@blacks) > (@whites)) ? (Dafny.Sequence<char>.FromString("The Black.")) : (((@blacks) < (@whites)) ? (Dafny.Sequence<char>.FromString("The White.")) : (Dafny.Sequence<char>.FromString("it's a tie."))));
    System.Console.Write(Dafny.Sequence<char>.FromString("\nFinal Score: "));
    System.Console.Write(@blacks);
    System.Console.Write(Dafny.Sequence<char>.FromString(" Black disks versus "));
    System.Console.Write(@whites);
    System.Console.Write(Dafny.Sequence<char>.FromString(" White disks."));
  }
  public static Dafny.Set<@_System.@__tuple_h2<BigInteger,BigInteger>> @ValidPositions() {
    return Dafny.Set<@_System.@__tuple_h2<BigInteger,BigInteger>>.FromElements(new @_System.@__tuple_h2<BigInteger,BigInteger>(new _System.@__tuple_h2____hMake2<BigInteger,BigInteger>(new BigInteger(0), new BigInteger(0))), new @_System.@__tuple_h2<BigInteger,BigInteger>(new _System.@__tuple_h2____hMake2<BigInteger,BigInteger>(new BigInteger(0), new BigInteger(1))), new @_System.@__tuple_h2<BigInteger,BigInteger>(new _System.@__tuple_h2____hMake2<BigInteger,BigInteger>(new BigInteger(0), new BigInteger(2))), new @_System.@__tuple_h2<BigInteger,BigInteger>(new _System.@__tuple_h2____hMake2<BigInteger,BigInteger>(new BigInteger(0), new BigInteger(3))), new @_System.@__tuple_h2<BigInteger,BigInteger>(new _System.@__tuple_h2____hMake2<BigInteger,BigInteger>(new BigInteger(0), new BigInteger(4))), new @_System.@__tuple_h2<BigInteger,BigInteger>(new _System.@__tuple_h2____hMake2<BigInteger,BigInteger>(new BigInteger(0), new BigInteger(5))), new @_System.@__tuple_h2<BigInteger,BigInteger>(new _System.@__tuple_h2____hMake2<BigInteger,BigInteger>(new BigInteger(0), new BigInteger(6))), new @_System.@__tuple_h2<BigInteger,BigInteger>(new _System.@__tuple_h2____hMake2<BigInteger,BigInteger>(new BigInteger(0), new BigInteger(7))), new @_System.@__tuple_h2<BigInteger,BigInteger>(new _System.@__tuple_h2____hMake2<BigInteger,BigInteger>(new BigInteger(1), new BigInteger(0))), new @_System.@__tuple_h2<BigInteger,BigInteger>(new _System.@__tuple_h2____hMake2<BigInteger,BigInteger>(new BigInteger(1), new BigInteger(1))), new @_System.@__tuple_h2<BigInteger,BigInteger>(new _System.@__tuple_h2____hMake2<BigInteger,BigInteger>(new BigInteger(1), new BigInteger(2))), new @_System.@__tuple_h2<BigInteger,BigInteger>(new _System.@__tuple_h2____hMake2<BigInteger,BigInteger>(new BigInteger(1), new BigInteger(3))), new @_System.@__tuple_h2<BigInteger,BigInteger>(new _System.@__tuple_h2____hMake2<BigInteger,BigInteger>(new BigInteger(1), new BigInteger(4))), new @_System.@__tuple_h2<BigInteger,BigInteger>(new _System.@__tuple_h2____hMake2<BigInteger,BigInteger>(new BigInteger(1), new BigInteger(5))), new @_System.@__tuple_h2<BigInteger,BigInteger>(new _System.@__tuple_h2____hMake2<BigInteger,BigInteger>(new BigInteger(1), new BigInteger(6))), new @_System.@__tuple_h2<BigInteger,BigInteger>(new _System.@__tuple_h2____hMake2<BigInteger,BigInteger>(new BigInteger(1), new BigInteger(7))), new @_System.@__tuple_h2<BigInteger,BigInteger>(new _System.@__tuple_h2____hMake2<BigInteger,BigInteger>(new BigInteger(2), new BigInteger(0))), new @_System.@__tuple_h2<BigInteger,BigInteger>(new _System.@__tuple_h2____hMake2<BigInteger,BigInteger>(new BigInteger(2), new BigInteger(1))), new @_System.@__tuple_h2<BigInteger,BigInteger>(new _System.@__tuple_h2____hMake2<BigInteger,BigInteger>(new BigInteger(2), new BigInteger(2))), new @_System.@__tuple_h2<BigInteger,BigInteger>(new _System.@__tuple_h2____hMake2<BigInteger,BigInteger>(new BigInteger(2), new BigInteger(3))), new @_System.@__tuple_h2<BigInteger,BigInteger>(new _System.@__tuple_h2____hMake2<BigInteger,BigInteger>(new BigInteger(2), new BigInteger(4))), new @_System.@__tuple_h2<BigInteger,BigInteger>(new _System.@__tuple_h2____hMake2<BigInteger,BigInteger>(new BigInteger(2), new BigInteger(5))), new @_System.@__tuple_h2<BigInteger,BigInteger>(new _System.@__tuple_h2____hMake2<BigInteger,BigInteger>(new BigInteger(2), new BigInteger(6))), new @_System.@__tuple_h2<BigInteger,BigInteger>(new _System.@__tuple_h2____hMake2<BigInteger,BigInteger>(new BigInteger(2), new BigInteger(7))), new @_System.@__tuple_h2<BigInteger,BigInteger>(new _System.@__tuple_h2____hMake2<BigInteger,BigInteger>(new BigInteger(3), new BigInteger(0))), new @_System.@__tuple_h2<BigInteger,BigInteger>(new _System.@__tuple_h2____hMake2<BigInteger,BigInteger>(new BigInteger(3), new BigInteger(1))), new @_System.@__tuple_h2<BigInteger,BigInteger>(new _System.@__tuple_h2____hMake2<BigInteger,BigInteger>(new BigInteger(3), new BigInteger(2))), new @_System.@__tuple_h2<BigInteger,BigInteger>(new _System.@__tuple_h2____hMake2<BigInteger,BigInteger>(new BigInteger(3), new BigInteger(3))), new @_System.@__tuple_h2<BigInteger,BigInteger>(new _System.@__tuple_h2____hMake2<BigInteger,BigInteger>(new BigInteger(3), new BigInteger(4))), new @_System.@__tuple_h2<BigInteger,BigInteger>(new _System.@__tuple_h2____hMake2<BigInteger,BigInteger>(new BigInteger(3), new BigInteger(5))), new @_System.@__tuple_h2<BigInteger,BigInteger>(new _System.@__tuple_h2____hMake2<BigInteger,BigInteger>(new BigInteger(3), new BigInteger(6))), new @_System.@__tuple_h2<BigInteger,BigInteger>(new _System.@__tuple_h2____hMake2<BigInteger,BigInteger>(new BigInteger(3), new BigInteger(7))), new @_System.@__tuple_h2<BigInteger,BigInteger>(new _System.@__tuple_h2____hMake2<BigInteger,BigInteger>(new BigInteger(4), new BigInteger(0))), new @_System.@__tuple_h2<BigInteger,BigInteger>(new _System.@__tuple_h2____hMake2<BigInteger,BigInteger>(new BigInteger(4), new BigInteger(1))), new @_System.@__tuple_h2<BigInteger,BigInteger>(new _System.@__tuple_h2____hMake2<BigInteger,BigInteger>(new BigInteger(4), new BigInteger(2))), new @_System.@__tuple_h2<BigInteger,BigInteger>(new _System.@__tuple_h2____hMake2<BigInteger,BigInteger>(new BigInteger(4), new BigInteger(3))), new @_System.@__tuple_h2<BigInteger,BigInteger>(new _System.@__tuple_h2____hMake2<BigInteger,BigInteger>(new BigInteger(4), new BigInteger(4))), new @_System.@__tuple_h2<BigInteger,BigInteger>(new _System.@__tuple_h2____hMake2<BigInteger,BigInteger>(new BigInteger(4), new BigInteger(5))), new @_System.@__tuple_h2<BigInteger,BigInteger>(new _System.@__tuple_h2____hMake2<BigInteger,BigInteger>(new BigInteger(4), new BigInteger(6))), new @_System.@__tuple_h2<BigInteger,BigInteger>(new _System.@__tuple_h2____hMake2<BigInteger,BigInteger>(new BigInteger(4), new BigInteger(7))), new @_System.@__tuple_h2<BigInteger,BigInteger>(new _System.@__tuple_h2____hMake2<BigInteger,BigInteger>(new BigInteger(5), new BigInteger(0))), new @_System.@__tuple_h2<BigInteger,BigInteger>(new _System.@__tuple_h2____hMake2<BigInteger,BigInteger>(new BigInteger(5), new BigInteger(1))), new @_System.@__tuple_h2<BigInteger,BigInteger>(new _System.@__tuple_h2____hMake2<BigInteger,BigInteger>(new BigInteger(5), new BigInteger(2))), new @_System.@__tuple_h2<BigInteger,BigInteger>(new _System.@__tuple_h2____hMake2<BigInteger,BigInteger>(new BigInteger(5), new BigInteger(3))), new @_System.@__tuple_h2<BigInteger,BigInteger>(new _System.@__tuple_h2____hMake2<BigInteger,BigInteger>(new BigInteger(5), new BigInteger(4))), new @_System.@__tuple_h2<BigInteger,BigInteger>(new _System.@__tuple_h2____hMake2<BigInteger,BigInteger>(new BigInteger(5), new BigInteger(5))), new @_System.@__tuple_h2<BigInteger,BigInteger>(new _System.@__tuple_h2____hMake2<BigInteger,BigInteger>(new BigInteger(5), new BigInteger(6))), new @_System.@__tuple_h2<BigInteger,BigInteger>(new _System.@__tuple_h2____hMake2<BigInteger,BigInteger>(new BigInteger(5), new BigInteger(7))), new @_System.@__tuple_h2<BigInteger,BigInteger>(new _System.@__tuple_h2____hMake2<BigInteger,BigInteger>(new BigInteger(6), new BigInteger(0))), new @_System.@__tuple_h2<BigInteger,BigInteger>(new _System.@__tuple_h2____hMake2<BigInteger,BigInteger>(new BigInteger(6), new BigInteger(1))), new @_System.@__tuple_h2<BigInteger,BigInteger>(new _System.@__tuple_h2____hMake2<BigInteger,BigInteger>(new BigInteger(6), new BigInteger(2))), new @_System.@__tuple_h2<BigInteger,BigInteger>(new _System.@__tuple_h2____hMake2<BigInteger,BigInteger>(new BigInteger(6), new BigInteger(3))), new @_System.@__tuple_h2<BigInteger,BigInteger>(new _System.@__tuple_h2____hMake2<BigInteger,BigInteger>(new BigInteger(6), new BigInteger(4))), new @_System.@__tuple_h2<BigInteger,BigInteger>(new _System.@__tuple_h2____hMake2<BigInteger,BigInteger>(new BigInteger(6), new BigInteger(5))), new @_System.@__tuple_h2<BigInteger,BigInteger>(new _System.@__tuple_h2____hMake2<BigInteger,BigInteger>(new BigInteger(6), new BigInteger(6))), new @_System.@__tuple_h2<BigInteger,BigInteger>(new _System.@__tuple_h2____hMake2<BigInteger,BigInteger>(new BigInteger(6), new BigInteger(7))), new @_System.@__tuple_h2<BigInteger,BigInteger>(new _System.@__tuple_h2____hMake2<BigInteger,BigInteger>(new BigInteger(7), new BigInteger(0))), new @_System.@__tuple_h2<BigInteger,BigInteger>(new _System.@__tuple_h2____hMake2<BigInteger,BigInteger>(new BigInteger(7), new BigInteger(1))), new @_System.@__tuple_h2<BigInteger,BigInteger>(new _System.@__tuple_h2____hMake2<BigInteger,BigInteger>(new BigInteger(7), new BigInteger(2))), new @_System.@__tuple_h2<BigInteger,BigInteger>(new _System.@__tuple_h2____hMake2<BigInteger,BigInteger>(new BigInteger(7), new BigInteger(3))), new @_System.@__tuple_h2<BigInteger,BigInteger>(new _System.@__tuple_h2____hMake2<BigInteger,BigInteger>(new BigInteger(7), new BigInteger(4))), new @_System.@__tuple_h2<BigInteger,BigInteger>(new _System.@__tuple_h2____hMake2<BigInteger,BigInteger>(new BigInteger(7), new BigInteger(5))), new @_System.@__tuple_h2<BigInteger,BigInteger>(new _System.@__tuple_h2____hMake2<BigInteger,BigInteger>(new BigInteger(7), new BigInteger(6))), new @_System.@__tuple_h2<BigInteger,BigInteger>(new _System.@__tuple_h2____hMake2<BigInteger,BigInteger>(new BigInteger(7), new BigInteger(7))));
  }
  public static void @canReverseUpFrom(Dafny.Map<@_System.@__tuple_h2<BigInteger,BigInteger>,@Disk> @b, @Disk @player, @_System.@__tuple_h2<BigInteger,BigInteger> @move, out Dafny.Sequence<@_System.@__tuple_h2<BigInteger,BigInteger>> @reversiblePositions)
  {
    @reversiblePositions = Dafny.Sequence<@_System.@__tuple_h2<BigInteger,BigInteger>>.Empty;
    { }
    @Disk @_55692_opponent = new @Disk();
    @Disk _out2;
    @__default.@getOpponent(@player, out _out2);
    @_55692_opponent = _out2;
    bool @_55693_dirValid = false;
    @_55693_dirValid = false;
    BigInteger @_55694_row = BigInteger.Zero;
    @_55694_row = ((@move).@dtor__0) - (new BigInteger(2));
    @reversiblePositions = Dafny.Sequence<@_System.@__tuple_h2<BigInteger,BigInteger>>.FromElements();
    if ((((@move).@dtor__0).@Equals(new BigInteger(0))) || ((!(@b).@Contains(new @_System.@__tuple_h2<BigInteger,BigInteger>(new _System.@__tuple_h2____hMake2<BigInteger,BigInteger>(((@move).@dtor__0) - (new BigInteger(1)), (@move).@dtor__1)))) || (!((@b).Select(new @_System.@__tuple_h2<BigInteger,BigInteger>(new _System.@__tuple_h2____hMake2<BigInteger,BigInteger>(((@move).@dtor__0) - (new BigInteger(1)), (@move).@dtor__1)))).@Equals(@_55692_opponent))))
    {
    }
    else
    {
      @reversiblePositions = (@reversiblePositions).@Concat(Dafny.Sequence<@_System.@__tuple_h2<BigInteger,BigInteger>>.FromElements(new @_System.@__tuple_h2<BigInteger,BigInteger>(new _System.@__tuple_h2____hMake2<BigInteger,BigInteger>(((@move).@dtor__0) - (new BigInteger(1)), (@move).@dtor__1))));
      { }
      { }
      while (((!(@_55693_dirValid)) && ((@_55694_row) >= (new BigInteger(0)))) && ((@b).@Contains(new @_System.@__tuple_h2<BigInteger,BigInteger>(new _System.@__tuple_h2____hMake2<BigInteger,BigInteger>(@_55694_row, (@move).@dtor__1)))))
      {
        if (((@b).Select(new @_System.@__tuple_h2<BigInteger,BigInteger>(new _System.@__tuple_h2____hMake2<BigInteger,BigInteger>(@_55694_row, (@move).@dtor__1)))).@Equals(@player))
        {
          @_55693_dirValid = true;
        }
        else
        {
          @reversiblePositions = (@reversiblePositions).@Concat(Dafny.Sequence<@_System.@__tuple_h2<BigInteger,BigInteger>>.FromElements(new @_System.@__tuple_h2<BigInteger,BigInteger>(new _System.@__tuple_h2____hMake2<BigInteger,BigInteger>(@_55694_row, (@move).@dtor__1))));
        }
        @_55694_row = (@_55694_row) - (new BigInteger(1));
        { }
      }
      if (@_55693_dirValid)
      {
      }
      else
      {
        @reversiblePositions = Dafny.Sequence<@_System.@__tuple_h2<BigInteger,BigInteger>>.FromElements();
      }
    }
  }
  public static void @getOpponent(@Disk @player, out @Disk @opp)
  {
    @opp = new @Disk();
  TAIL_CALL_START: ;
    if ((@player).@Equals(new @Disk(new Disk_White())))
    {
      @opp = new @Disk(new Disk_Black());
    }
    else
    {
      @opp = new @Disk(new Disk_White());
    }
  }
  public static void @canReverseInDir(Dafny.Map<@_System.@__tuple_h2<BigInteger,BigInteger>,@Disk> @b, @Disk @player, @_System.@__tuple_h2<BigInteger,BigInteger> @move, @Direction @dir, out bool @is)
  {
    @is = false;
    { }
    if ((@dir).@Equals(new @Direction(new Direction_Up())))
    {
    }
    else
    if ((@dir).@Equals(new @Direction(new Direction_UpRight())))
    {
    }
    else
    if ((@dir).@Equals(new @Direction(new Direction_Right())))
    {
    }
    else
    if ((@dir).@Equals(new @Direction(new Direction_DownRight())))
    {
    }
    else
    if ((@dir).@Equals(new @Direction(new Direction_Down())))
    {
    }
    else
    if ((@dir).@Equals(new @Direction(new Direction_DownLeft())))
    {
    }
    else
    if ((@dir).@Equals(new @Direction(new Direction_Left())))
    {
    }
    else
    if ((@dir).@Equals(new @Direction(new Direction_UpLeft())))
    {
    }
    else
    {
      @is = false;
    }
/* Compilation error: an assume statement cannot be compiled (line 407) */
    { }
  }
  public static void @SelectBlackMove(Dafny.Map<@_System.@__tuple_h2<BigInteger,BigInteger>,@Disk> @b, Dafny.Set<@_System.@__tuple_h2<BigInteger,BigInteger>> @moves, out @_System.@__tuple_h2<BigInteger,BigInteger> @pos)
  {
    @pos = new @_System.@__tuple_h2<BigInteger,BigInteger>();
  TAIL_CALL_START: ;
    foreach (var _assign_such_that_0 in (@moves).Elements) { @pos = _assign_such_that_0;
      if ((@moves).@Contains(@pos)) {
        goto _ASSIGN_SUCH_THAT_0;
      }
    }
    throw new System.Exception("assign-such-that search produced no value (line 416)");
    _ASSIGN_SUCH_THAT_0: ;
  }
  public static void @SelectWhiteMove(Dafny.Map<@_System.@__tuple_h2<BigInteger,BigInteger>,@Disk> @b, Dafny.Set<@_System.@__tuple_h2<BigInteger,BigInteger>> @moves, out @_System.@__tuple_h2<BigInteger,BigInteger> @pos)
  {
    @pos = new @_System.@__tuple_h2<BigInteger,BigInteger>();
  TAIL_CALL_START: ;
    foreach (var _assign_such_that_1 in (@moves).Elements) { @pos = _assign_such_that_1;
      if ((@moves).@Contains(@pos)) {
        goto _ASSIGN_SUCH_THAT_1;
      }
    }
    throw new System.Exception("assign-such-that search produced no value (line 425)");
    _ASSIGN_SUCH_THAT_1: ;
  }
  public static void @InitBoard(out Dafny.Map<@_System.@__tuple_h2<BigInteger,BigInteger>,@Disk> @b)
  {
    @b = Dafny.Map<@_System.@__tuple_h2<BigInteger,BigInteger>,@Disk>.Empty;
  TAIL_CALL_START: ;
    @b = Dafny.Map<@_System.@__tuple_h2<BigInteger,BigInteger>,@Disk>.FromElements(new Dafny.Pair<@_System.@__tuple_h2<BigInteger,BigInteger>,@Disk>(new @_System.@__tuple_h2<BigInteger,BigInteger>(new _System.@__tuple_h2____hMake2<BigInteger,BigInteger>(new BigInteger(3), new BigInteger(3))),new @Disk(new Disk_White())), new Dafny.Pair<@_System.@__tuple_h2<BigInteger,BigInteger>,@Disk>(new @_System.@__tuple_h2<BigInteger,BigInteger>(new _System.@__tuple_h2____hMake2<BigInteger,BigInteger>(new BigInteger(3), new BigInteger(4))),new @Disk(new Disk_Black())), new Dafny.Pair<@_System.@__tuple_h2<BigInteger,BigInteger>,@Disk>(new @_System.@__tuple_h2<BigInteger,BigInteger>(new _System.@__tuple_h2____hMake2<BigInteger,BigInteger>(new BigInteger(4), new BigInteger(3))),new @Disk(new Disk_Black())), new Dafny.Pair<@_System.@__tuple_h2<BigInteger,BigInteger>,@Disk>(new @_System.@__tuple_h2<BigInteger,BigInteger>(new _System.@__tuple_h2____hMake2<BigInteger,BigInteger>(new BigInteger(4), new BigInteger(4))),new @Disk(new Disk_White())));
  }
  public static void @TotalScore(Dafny.Map<@_System.@__tuple_h2<BigInteger,BigInteger>,@Disk> @b, out BigInteger @blacks, out BigInteger @whites)
  {
    @blacks = BigInteger.Zero;
    @whites = BigInteger.Zero;
    Dafny.Set<@_System.@__tuple_h2<BigInteger,BigInteger>> @_55695_positionsToCheck = Dafny.Set<@_System.@__tuple_h2<BigInteger,BigInteger>>.Empty;
    @_55695_positionsToCheck = @__default.@ValidPositions();
    { }
    { }
    @whites = new BigInteger(0);
    @blacks = new BigInteger(0);
    { }
    while (!(@_55695_positionsToCheck).@Equals(Dafny.Set<@_System.@__tuple_h2<BigInteger,BigInteger>>.FromElements()))
    {
      { }
      @_System.@__tuple_h2<BigInteger,BigInteger> @_55696_pos = new @_System.@__tuple_h2<BigInteger,BigInteger>();
      foreach (var _assign_such_that_2 in (@_55695_positionsToCheck).Elements) { @_55696_pos = _assign_such_that_2;
        if ((@_55695_positionsToCheck).@Contains(@_55696_pos)) {
          goto _ASSIGN_SUCH_THAT_2;
        }
      }
      throw new System.Exception("assign-such-that search produced no value (line 451)");
      _ASSIGN_SUCH_THAT_2: ;
      @_55695_positionsToCheck = (@_55695_positionsToCheck).@Difference(Dafny.Set<@_System.@__tuple_h2<BigInteger,BigInteger>>.FromElements(@_55696_pos));
      { }
      if ((@b).@Contains(@_55696_pos))
      {
        if (((@b).Select(@_55696_pos)).@Equals(new @Disk(new Disk_White())))
        {
          { }
          { }
          @whites = (@whites) + (new BigInteger(1));
          { }
/* Compilation error: an assume statement cannot be compiled (line 461) */
          { }
        }
        else
        if (((@b).Select(@_55696_pos)).@Equals(new @Disk(new Disk_White())))
        {
          { }
          { }
          @blacks = (@blacks) + (new BigInteger(1));
          { }
          { }
        }
        else
        { }
      }
      else
      { }
    }
    { }
/* Compilation error: an assume statement cannot be compiled (line 480) */
    { }
    { }
    { }
  }
  public static void @FindAllLegalDirectionsFrom(Dafny.Map<@_System.@__tuple_h2<BigInteger,BigInteger>,@Disk> @b, @Disk @player, @_System.@__tuple_h2<BigInteger,BigInteger> @move, out Dafny.Set<@Direction> @directions)
  {
    @directions = Dafny.Set<@Direction>.Empty;
    { }
    Dafny.Set<@Direction> @_55697_directionsToCheck = Dafny.Set<@Direction>.Empty;
    @_55697_directionsToCheck = Dafny.Set<@Direction>.FromElements(new @Direction(new Direction_Up()), new @Direction(new Direction_UpRight()), new @Direction(new Direction_Right()), new @Direction(new Direction_DownRight()), new @Direction(new Direction_Down()), new @Direction(new Direction_DownLeft()), new @Direction(new Direction_Left()), new @Direction(new Direction_UpLeft()));
    @directions = Dafny.Set<@Direction>.FromElements();
    while (!(@_55697_directionsToCheck).@Equals(Dafny.Set<@Direction>.FromElements()))
    {
      @Direction @_55698_dir = new @Direction();
      foreach (var _assign_such_that_3 in (@_55697_directionsToCheck).Elements) { @_55698_dir = _assign_such_that_3;
        if ((@_55697_directionsToCheck).@Contains(@_55698_dir)) {
          goto _ASSIGN_SUCH_THAT_3;
        }
      }
      throw new System.Exception("assign-such-that search produced no value (line 498)");
      _ASSIGN_SUCH_THAT_3: ;
      bool @_55699_isReversible = false;
      bool _out3;
      @__default.@canReverseInDir(@b, @player, @move, @_55698_dir, out _out3);
      @_55699_isReversible = _out3;
      if (@_55699_isReversible)
      {
        @directions = (@directions).@Union(Dafny.Set<@Direction>.FromElements(@_55698_dir));
      }
      else
      { }
      @_55697_directionsToCheck = (@_55697_directionsToCheck).@Difference(Dafny.Set<@Direction>.FromElements(@_55698_dir));
    }
/* Compilation error: an assume statement cannot be compiled (line 509) */
    { }
    { }
  }
/* Compilation error: Method _module._default.FindAllReversiblePositionsFrom has no body */
/* Compilation error: Method _module._default.FindAllLegalMoves has no body */
/* Compilation error: Method _module._default.PerformMove has no body */
}
