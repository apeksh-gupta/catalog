// shamir_verify.cpp
// Compile: g++ -std=c++17 -O2 shamir_verify.cpp -o shamir_verify
// Requires: Boost.Multiprecision header (usually available with g++)
// Run: ./shamir_verify < testcases.json

#include <bits/stdc++.h>
#include <boost/multiprecision/cpp_int.hpp>
using namespace std;
using boost::multiprecision::cpp_int;

// ---------- Fraction with cpp_int ----------
struct Frac {
    cpp_int num;
    cpp_int den; // always > 0
    Frac(cpp_int n = 0, cpp_int d = 1) {
        if (d == 0) throw runtime_error("zero denominator");
        if (d < 0) { n = -n; d = -d; }
        cpp_int g = gcd_abs(n < 0 ? -n : n, d);
        num = n / g; den = d / g;
    }
    static cpp_int gcd_abs(cpp_int a, cpp_int b) {
        if (a < 0) a = -a;
        if (b < 0) b = -b;
        while (b != 0) {
            cpp_int r = a % b;
            a = b;
            b = r;
        }
        return a;
    }
    Frac operator+(const Frac &o) const { return Frac(num * o.den + o.num * den, den * o.den); }
    Frac operator-(const Frac &o) const { return Frac(num * o.den - o.num * den, den * o.den); }
    Frac operator*(const Frac &o) const { return Frac(num * o.num, den * o.den); }
    Frac operator/(const Frac &o) const {
        if (o.num == 0) throw runtime_error("division by zero fraction");
        return Frac(num * o.den, den * o.num);
    }
    bool isInteger() const { return den == 1; }
};

// ---------- Utility: trim spaces ----------
static inline void trim(string &s) {
    size_t a = 0; while (a < s.size() && isspace((unsigned char)s[a])) ++a;
    size_t b = s.size(); while (b > a && isspace((unsigned char)s[b-1])) --b;
    s = s.substr(a, b - a);
}

// ---------- Parse ints from a JSON-like substring (very targeted) ----------
long long parse_small_int_after_key(const string &s, size_t pos_key) {
    size_t p = s.find(':', pos_key);
    if (p == string::npos) throw runtime_error("invalid json structure (int)");
    ++p;
    while (p < s.size() && isspace((unsigned char)s[p])) ++p;
    size_t q = p;
    while (q < s.size() && (s[q] == '-' || isdigit((unsigned char)s[q]))) ++q;
    string num = s.substr(p, q - p);
    trim(num);
    return stoll(num);
}

// parse a quoted string value after key (e.g. "value": "abc")
string parse_quoted_after_key(const string &s, size_t pos_key) {
    size_t p = s.find(':', pos_key);
    if (p == string::npos) throw runtime_error("invalid json structure (str)");
    p++;
    size_t q = s.find('"', p);
    if (q == string::npos) throw runtime_error("invalid json: missing opening quote");
    size_t r = s.find('"', q + 1);
    if (r == string::npos) throw runtime_error("invalid json: missing closing quote");
    return s.substr(q + 1, r - (q + 1));
}

// ---------- decode arbitrary-base string to cpp_int ----------
cpp_int parse_in_base_cpp(const string &s_raw, int base) {
    cpp_int val = 0;
    for (char ch : s_raw) {
        if (isspace((unsigned char)ch)) continue;
        int d = -1;
        if (ch >= '0' && ch <= '9') d = ch - '0';
        else if (ch >= 'a' && ch <= 'z') d = ch - 'a' + 10;
        else if (ch >= 'A' && ch <= 'Z') d = ch - 'A' + 10;
        else throw runtime_error(string("invalid digit: ") + ch);
        if (d < 0 || d >= base) throw runtime_error("digit >= base in parse_in_base_cpp");
        val *= base;
        val += d;
    }
    return val;
}

// ---------- Extract JSON objects from input string ----------
vector<string> split_json_objects(const string &input) {
    vector<string> objs;
    int depth = 0;
    int start = -1;
    for (size_t i = 0; i < input.size(); ++i) {
        char c = input[i];
        if (c == '{') {
            if (depth == 0) start = (int)i;
            depth++;
        } else if (c == '}') {
            depth--;
            if (depth == 0 && start != -1) {
                objs.push_back(input.substr(start, i - start + 1));
                start = -1;
            }
        }
    }
    return objs;
}

// ---------- Solve Vandermonde via Gaussian elimination ----------
bool interpolate_and_check(const vector<int> &xs, const vector<cpp_int> &ys, vector<Frac> &out_coeff) {
    int k = xs.size();
    vector<vector<Frac>> A(k, vector<Frac>(k + 1, Frac(0, 1)));
    for (int i = 0; i < k; ++i) {
        cpp_int power = 1;
        for (int j = 0; j < k; ++j) {
            A[i][j] = Frac(power, 1);
            power *= xs[i];
        }
        A[i][k] = Frac(ys[i], 1);
    }

    for (int col = 0, row = 0; col < k && row < k; ++col, ++row) {
        int sel = row;
        for (int r = row; r < k; ++r) {
            if (A[r][col].num != 0) { sel = r; break; }
        }
        if (A[sel][col].num == 0) return false;
        if (sel != row) swap(A[sel], A[row]);

        Frac pivot = A[row][col];
        for (int c = col; c <= k; ++c) A[row][c] = A[row][c] / pivot;

        for (int r = 0; r < k; ++r) {
            if (r == row) continue;
            Frac factor = A[r][col];
            if (factor.num == 0) continue;
            for (int c = col; c <= k; ++c) {
                A[r][c] = A[r][c] - factor * A[row][c];
            }
        }
    }

    out_coeff.assign(k, Frac(0, 1));
    for (int i = 0; i < k; ++i) out_coeff[i] = A[i][k];

    // 🔴 FIX: allow negative or zero coefficients
    for (int i = 0; i < k; ++i) {
        if (!out_coeff[i].isInteger()) return false;
    }
    return true;
}

// ---------- Iterate combinations ----------
bool find_valid_constant(const vector<int> &xs_full, const vector<cpp_int> &ys_full, int k, cpp_int &constant_out) {
    int n = (int)xs_full.size();
    if (k > n) return false;

    vector<int> choose(n, 0);
    for (int i = 0; i < k; ++i) choose[i] = 1;
    sort(choose.begin(), choose.end(), greater<int>());

    do {
        vector<int> xs;
        vector<cpp_int> ys;
        xs.reserve(k); ys.reserve(k);
        for (int i = 0; i < n; ++i) if (choose[i]) { xs.push_back(xs_full[i]); ys.push_back(ys_full[i]); }
        vector<Frac> coeffs;
        bool ok = interpolate_and_check(xs, ys, coeffs);
        if (ok) {
            constant_out = coeffs[0].num;
            return true;
        }
    } while (prev_permutation(choose.begin(), choose.end()));
    return false;
}

size_t find_key(const string &s, const string &key, size_t startpos = 0) {
    return s.find(key, startpos);
}

string cpp_int_to_string(const cpp_int &v) {
    string s;
    cpp_int t = v;
    if (t == 0) return "0";
    bool neg = false;
    if (t < 0) { neg = true; t = -t; }
    while (t > 0) {
        int digit = (int)(t % 10);
        s.push_back(char('0' + digit));
        t /= 10;
    }
    if (neg) s.push_back('-');
    reverse(s.begin(), s.end());
    return s;
}

// ---------- Parse one JSON ----------
bool solve_one_json_string(const string &obj_str, string &out_constant_str) {
    size_t pos_keys = obj_str.find("\"keys\"");
    if (pos_keys == string::npos) return false;
    size_t pos_n = obj_str.find("\"n\"", pos_keys);
    size_t pos_k = obj_str.find("\"k\"", pos_keys);
    if (pos_n == string::npos || pos_k == string::npos) return false;
    long long n = parse_small_int_after_key(obj_str, pos_n);
    long long k = parse_small_int_after_key(obj_str, pos_k);
    if (n <= 0 || k <= 0) return false;

    vector<int> xs;
    vector<cpp_int> ys;
    xs.reserve(n); ys.reserve(n);

    for (long long idx = 1; idx <= n; ++idx) {
        string key = "\"" + to_string(idx) + "\"";
        size_t pos = obj_str.find(key);
        if (pos == string::npos) continue;
        size_t pos_base_key = obj_str.find("\"base\"", pos);
        if (pos_base_key == string::npos) return false;
        string base_str = parse_quoted_after_key(obj_str, pos_base_key);
        int base = 10;
        try {
            base = stoi(base_str);
        } catch (...) {
            size_t colon = obj_str.find(':', pos_base_key);
            if (colon == string::npos) return false;
            size_t p = colon + 1; while (p < obj_str.size() && isspace((unsigned char)obj_str[p])) ++p;
            size_t q = p; while (q < obj_str.size() && (isdigit((unsigned char)obj_str[q]) || obj_str[q] == '-')) ++q;
            string num = obj_str.substr(p, q - p);
            trim(num);
            base = stoi(num);
        }
        size_t pos_val_key = obj_str.find("\"value\"", pos);
        if (pos_val_key == string::npos) return false;
        string val = parse_quoted_after_key(obj_str, pos_val_key);

        cpp_int y = parse_in_base_cpp(val, base);
        xs.push_back((int)idx);
        ys.push_back(y);
    }

    if ((int)xs.size() < k) return false;

    cpp_int constant;
    bool found = find_valid_constant(xs, ys, (int)k, constant);
    if (!found) return false;
    out_constant_str = cpp_int_to_string(constant);
    return true;
}

// ---------- Main ----------
int main() {
    ios::sync_with_stdio(false);
    cin.tie(nullptr);

    string input;
    {
        ostringstream ss;
        ss << cin.rdbuf();
        input = ss.str();
    }
    if (input.empty()) {
        cerr << "No input provided\n";
        return 1;
    }

    vector<string> objects = split_json_objects(input);
    if (objects.empty()) {
        cerr << "No JSON objects found in input\n";
        return 1;
    }

    bool anyPrinted = false;
    for (auto &obj : objects) {
        string cstr;
        bool ok = solve_one_json_string(obj, cstr);
        if (ok) {
            cout << cstr << "\n";
            anyPrinted = true;
        } else {
            cout << "ERROR\n";
        }
    }

    return anyPrinted ? 0 : 1;
}
