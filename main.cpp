#include <iostream>
#include <fstream>
#include <map>
#include <regex>
#include <vector>
using namespace std;
typedef vector<int> vi;
typedef long long ll;

enum type {
    RR = 0,
    RM = 1,
    B = 2,
    C = 3
};

enum code_e {
    HALT = 0,
    SVC = 1,
    ADD = 2,
    SUB = 3,
    MUL = 4,
    DIV = 5,
    MOD = 6,
    AND = 7,
    OR = 8,
    XOR = 9,
    NAND = 10,
    ADDD = 12,
    SUBD = 13,
    MULD = 14,
    DIVD = 15,
    ITOD = 16,
    DTOI = 17,
    SHL = 18,
    SHR = 19,
    BL = 20,
    CMP = 22,
    CMPD = 23,
    CNE = 25,
    CEQ = 26,
    CLE = 27,
    CLT = 28,
    CGE = 29,
    CGT = 30,
    LD = 31,
    ST = 32,
    SKIP = -1
};

struct command {
    int code;
    int type;

    void (*func)(const vi&);
};

union cvt_ll_dbl {
    double dbl;
    struct { long long ll; };
};

map<string, int> map_of_codes = { {"halt", HALT}, {"svc", SVC}, {"add", ADD}, {"sub", SUB},
                                  {"mul", MUL}, {"div", DIV}, {"mod", MOD}, {"and", AND},
                                  {"or", OR}, {"xor", XOR}, {"nand", NAND}, {"addd", ADDD},
                                  {"subd", SUBD}, {"muld", MULD}, {"divd", DIVD}, {"itod", ITOD},
                                  {"dtoi", DTOI}, {"bl", BL}, {"cmp", CMP}, {"cmpd", CMPD},
                                  {"cne", CNE}, {"ceq", CEQ}, {"cle", CLE}, {"clt", CLT},
                                  {"cge", CGE}, {"cgt", CGT}, {"ld", LD}, {"st", ST} };

static long long regs[32] = {0};
map<string, int> spec = { {"rz", 27}, {"fp", 28}, {"sp", 29}, {"lr", 30}, {"pc", 31} };

int cmp_flag = 0;
bool exit0 = false;

static vector<pair<long long, vector<int>>> mem (1 << 21);     // command and {vars}
static map<string, int> marks;                                  // stores the marks (marks -> address)
static map<string, double> consts;                              // stores constants

void halt (const vi& arr) {
    exit0 = true;
}

void svc (const vi& arr) {
    switch (arr[2]) {
        case 0:
            exit0 = true;
            break;
        case 100: {
            long long ll; scanf("%lld", &ll);
            regs[arr[0]] = ll;
            break;
        }
        case 101: {
            double dbl; scanf("%lf", &dbl);
            regs[arr[0]] = *(long long*) &dbl;
            break;
        }
        case 102: {
            printf("%lld", regs[arr[0]]);
            break;
        }
        case 103:
            printf("%lg", *(double*) &regs[arr[0]]);
            break;
        case 104: {
            char ch; scanf("%c", &ch);
            regs[arr[0]] = ch;
            break;
        }
        case 105:
            printf("%c", static_cast<char>(regs[arr[0]]));
            break;
    }
}

void add (const vi& arr) {
    if (arr[1] == 27)
        regs[arr[0]] = arr[2];
    else
        regs[arr[0]] = regs[arr[1]] + (regs[arr[2]] * (1 << arr[3])) + arr[4];
}

void sub (const vi& arr) {
    if (arr[1] == 27)
        regs[arr[0]] = arr[2];
    else
        regs[arr[0]] = regs[arr[1]] - ((regs[arr[2]] * (1 << arr[3])) + arr[4]);
}

void mul (const vi& arr) {
    if (arr[1] == 27)
        regs[arr[0]] *= arr[2];
    else
        regs[arr[0]] = regs[arr[1]] * ((regs[arr[2]] * (1 << arr[3])) + arr[4]);
}

void div (const vi& arr) {
    if (arr[1] == 27)
        regs[arr[0]] /= arr[2];
    else
        regs[arr[0]] = regs[arr[1]] / ((regs[arr[2]] * (1 << arr[3])) + arr[4]);
}

void mod (const vi& arr) {
    if (arr[1] == 27)
        regs[arr[0]] %= arr[2];
    else
        regs[arr[0]] = regs[arr[1]] % ((regs[arr[2]] * (1 << arr[3])) + arr[4]);
}

void and_ (const vi& arr) {
    if (arr[1] == 27)
        regs[arr[0]] &= arr[2];
    else
        regs[arr[0]] = regs[arr[1]] & ((regs[arr[2]] * (1 << arr[3])) + arr[4]);
}

void or_ (const vi& arr) {
    if (arr[1] == 27)
        regs[arr[0]] |= arr[2];
    else
        regs[arr[0]] = regs[arr[1]] | ((regs[arr[2]] * (1 << arr[3])) + arr[4]);
}

void xor_ (const vi& arr) {
    if (arr[1] == 27)
        regs[arr[0]] ^= arr[2];
    else
        regs[arr[0]] = regs[arr[1]] ^ ((regs[arr[2]] * (1 << arr[3])) + arr[4]);
}

void nand_ (const vi& arr) {
    if (arr[1] == 27)
        regs[arr[0]] = ~(regs[arr[0]] & arr[2]);
    else
        regs[arr[0]] = ~(regs[arr[1]] + ((regs[arr[2]] * (1 << arr[3])) + arr[4]));
}

void shl (const vi& arr) {
    if (arr[1] == 27)
        regs[arr[0]] <<= arr[2];
    else
        regs[arr[0]] = regs[arr[1]] << ((regs[arr[2]] * (1 << arr[3]) + arr[4]) & 0x3F);
}

void shr (const vi& arr) {
    if (arr[1] == 27)
        regs[arr[0]] >>= arr[2];
    else
        regs[arr[0]] = regs[arr[1]] >> ((regs[arr[2]] * (1 << arr[3]) + arr[4]) & 0x3F);
}

// addd r1 r1 r2 3 5 <=> r1 = r1 + r2 * (1 << 3) + 5
//                       0    1    2          3    4
void addd (const vi& arr) {
    cvt_ll_dbl u{};
    u.ll = regs[arr[2]]; double dbl = u.dbl;
    dbl = dbl * (1 << arr[3]) + arr[4];
    u.ll = regs[arr[1]]; u.dbl += dbl;
    regs[arr[0]] = u.ll;
}

void subd (const vi& arr) {
    cvt_ll_dbl u{};
    u.ll = regs[arr[2]]; double dbl = u.dbl;
    dbl = dbl * (1 << arr[3]) + arr[4];
    u.ll = regs[arr[1]]; u.dbl -= dbl;
    regs[arr[0]] = u.ll;
}

void muld (const vi& arr) {
    cvt_ll_dbl u{};
    u.ll = regs[arr[2]]; double dbl = u.dbl;
    dbl = dbl * (1 << arr[3]) + arr[4];
    u.ll = regs[arr[1]]; u.dbl *= dbl;
    regs[arr[0]] = u.ll;
}

void divd (const vi& arr) {
    cvt_ll_dbl u{};
    u.ll = regs[arr[2]]; double dbl = u.dbl;
    dbl = dbl * (1 << arr[3]) + arr[4];
    u.ll = regs[arr[1]]; u.dbl /= dbl;
    regs[arr[0]] = u.ll;
}

// TODO: itod and dtoi think about
void itod (const vi& arr) {
    cvt_ll_dbl u{};
    u.dbl = static_cast<double>(regs[arr[1]] + regs[arr[2]] * (1 << arr[3]) + arr[4]);
    regs[arr[0]] = u.ll;
}

void dtoi (const vi& arr) {
    cvt_ll_dbl u{};
    u.ll = regs[arr[2]]; double dbl = u.dbl;
    dbl = dbl * (1 << arr[3]) + arr[4];
    u.ll = regs[arr[1]]; u.dbl += dbl;
    regs[arr[0]] = u.ll;
}

void bl (const vi& arr) {
    if (arr[0] == 27) {

    }

    regs[31] = regs[arr[0]] + (regs[arr[1]] * (1 << arr[2])) + arr[3] - 1;
}

void cmp (const vi& arr) {
    if (regs[arr[0]] > regs[arr[1]])
        cmp_flag = 1;
    else if (regs[arr[0]] == regs[arr[1]])
        cmp_flag = 0;
    else
        cmp_flag = -1;
}

void cmpd (const vi& arr) {
    cvt_ll_dbl u{}, u2{};
    u.ll = arr[0]; u2.ll = arr[1];

    if (u.dbl > u2.dbl)
        cmp_flag = 1;
    else if (u.dbl == u2.dbl)
        cmp_flag = 0;
    else
        cmp_flag = -1;
}

void cne (const vi& arr) {
    if (cmp_flag) {
        if (arr[0] == spec["pc"])
            regs[arr[0]] = arr[1];
        else
            regs[arr[0]] = regs[arr[1]] + regs[arr[2]] * (1 << arr[3]) + arr[4];
    }
}

void ceq (const vi& arr) {
    if (!cmp_flag) {
        if (arr[0] == spec["pc"])
            regs[arr[0]] = arr[1];
        else
            regs[arr[0]] = regs[arr[1]] + regs[arr[2]] * (1 << arr[3]) + arr[4];
    }
}

void cle (const vi& arr) {
    if (cmp_flag != 1) {
        if (arr[0] == spec["pc"])
            regs[arr[0]] = arr[1];
        else
            regs[arr[0]] = regs[arr[1]] + regs[arr[2]] * (1 << arr[3]) + arr[4];
    }
}

void clt (const vi& arr) {
    if (cmp_flag == -1) {
        if (arr[0] == spec["pc"])
            regs[arr[0]] = arr[1];
        else
            regs[arr[0]] = regs[arr[1]] + regs[arr[2]] * (1 << arr[3]) + arr[4];
    }
}

void cge (const vi& arr) {
    if (cmp_flag != -1) {
        if (arr[0] == spec["pc"])
            regs[arr[0]] = arr[1];
        else
            regs[arr[0]] = regs[arr[1]] + regs[arr[2]] * (1 << arr[3]) + arr[4];
    }
}

void cgt (const vi& arr) {
    if (cmp_flag == 1) {
        if (arr[0] == spec["pc"])
            regs[arr[0]] = arr[1];
        else
            regs[arr[0]] = regs[arr[1]] + regs[arr[2]] * (1 << arr[3]) + arr[4];
    }
}

void ld (const vi& arr) {
    if (arr[1] != spec["sp"])
    //if (arr[1] == spec["pc"] || arr[1] == spec["rz"])
        regs[arr[0]] = mem[regs[arr[1]] + arr[2]].first;
    else if (arr[1] == spec["sp"]) {
        regs[arr[0]] = mem[regs[arr[1]] + arr[2]].first;
        regs[arr[1]] += arr[2];
    }
    //else
    //    regs[arr[0]] = mem[regs[arr[1]] + arr[2]].first;
}

void st (const vi& arr) {
    if (arr[1] != spec["sp"])
        mem[regs[arr[1]] + arr[2]].first = regs[arr[0]];
    else {
        regs[spec["sp"]] -= arr[2];
        mem[regs[arr[1]]].first = regs[arr[0]];
    }
}

void skip (const vi& arr) {

}

vector<command> funcs {
        {HALT, RR, halt}, {SVC, RR, svc}, {ADD, RR, add},
        {SUB, RR, sub}, {MUL, RR, mul}, {DIV, RR, div},
        {MOD, RR, mod}, {AND, RR, and_}, {OR, RR, or_},
        {XOR, RR, xor_}, {NAND, RR, nand_}, {SKIP, RR, skip},
        {ADDD, RR, addd}, {SUBD, RR, subd}, {MULD, RR, muld},
        {DIVD, RR, divd}, {ITOD, RR, itod}, {DTOI, RR, dtoi},
        {SHL, RR, shl}, {SHR, RR, shr}, {BL, B, bl},
        {SKIP, RR, skip}, {CMP, RR, cmp}, {CMPD, RR, cmpd},
        {SKIP, RR, skip}, {CNE, C, cne}, {CEQ, C, ceq},
        {CLE, C, cle}, {CLT, C, clt}, {CGE, C, cge},
        {CGT, C, cgt}, {LD, RM, ld}, {ST, RM, st}
};

void delete_whitespaces(string* str) {
    while (true) {
        char c = (*str)[0];
        if (c == ' ' || c == '\t')
            (*str).erase(0, 1);
        else
            return;
    }
}

int reg_to_int(string reg) {
    if (!isdigit(reg[1]))
        return spec[reg];

    if (reg.length() == 2)
        return reg[1] - '0';
    else
        return 10 * reg[1] + reg[2] - 11 * '0';
}

void fill_line (const string& line, int pc) {
    if (line.empty()) {
        mem[pc].first = SKIP;
        return;
    }

    regex rr_command(R"(^\w+\s*(\w+),?\s*(\w+),?\s*(\w+),?\s*(\d+)?,?\s*(-?\d+)?)"),
          rm_command(R"(^\w+\s*(\w+),?\s*(\w+),?\s*(\w+),?\s*(\d+)?,?\s*(-?\d+)?)"),
          b_command(R"(^\w+\s*(\w+),?\s*(\w+)?,?\s*(\d+)?,?\s*(\d+)?)");

    regex get_code("^(\\w+) ");
    smatch storer;
    regex_search(line, storer, get_code);

    if (storer.empty()) {
        mem[pc].first = SKIP;
        return;
    }

    int cur = map_of_codes[storer[1].str()];
    switch (funcs[cur].type) {
        case RR: {
            regex_search(line, storer, rr_command);
            if (storer[2] == "rz")
                mem[pc].second = {reg_to_int(storer[1]), 27, stoi(storer[3]), 0, 0};
            else
                mem[pc].second = {reg_to_int(storer[1]), reg_to_int(storer[2]), reg_to_int(storer[3]), stoi(storer[4]), stoi(storer[5])};
            break;
        }
        case RM: {
            regex_search(line, storer, rm_command);
            if (storer[2] == "rz" || storer[2] == "pc" || storer[2] == "sp")
                mem[pc].second = {reg_to_int(storer[1]), spec[storer[2]], stoi(storer[3]), 0, 0};
            else if (storer[3] == "rz")
                mem[pc].second = {reg_to_int(storer[1]), reg_to_int(storer[2]), 27, stoi(storer[4]), 0};
            else
                mem[pc].second = {reg_to_int(storer[1]), reg_to_int(storer[2]), reg_to_int(storer[3]), stoi(storer[4]), stoi(storer[5])};
            break;
        }
        case B: {
            regex_search(line, storer, b_command);
            if (storer[1] == "rz" || storer[1] == "sp")
                mem[pc].second = {spec[storer[1]], stoi(storer[2]), 0, 0, 0};
            else if (storer[2].str().empty())
                mem[pc].second = {marks[storer[1]], 0, 0, 0, 0};
            else
                mem[pc].second = {reg_to_int(storer[1]), reg_to_int(storer[2]), stoi(storer[3]), stoi(storer[4]), 0};
            break;
        }
        case C: {
            regex_search(line, storer, rr_command);
            if (storer[1] == "pc" && !isdigit(storer[2].str()[0]))
                mem[pc].second = {spec["pc"], marks[storer[2]], 0, 0, 0};
            else
                mem[pc].second = {reg_to_int(storer[1]), reg_to_int(storer[2]), reg_to_int(storer[3]), stoi(storer[4]), stoi(storer[5])};
        }
    }

    mem[pc].first = funcs[cur].code;
}

string arr[200];
int main() {
    int iter = 0, start_pos = 0, end_pos = 0;
    string line;

    ifstream fs;
    fs.open("input.fasm");
    if (fs.is_open()) {
        smatch storer;

        while (getline(fs, line)) {
            line = regex_replace(line, regex(R"(;.+)"), "");

            if (regex_match(line, storer, regex("^(\\w+): ?(word|double) ([0-9\\.]+)"))) {
                consts[storer[1].str()] = stod(storer[3].str());
                // TODO: Finish word byte and double
            } else if (line.find(':') != -1) {
                regex_search(line, storer, regex("^([a-zA-Z0-9]+):\\s*"));
                marks[storer[1].str()] = iter;
                line = storer.suffix();
            }

            if (regex_match(line, storer, regex("\\s*end (\\w+)"))) {
                start_pos = marks[storer[1].str()], end_pos = iter;
                break;
            }

            delete_whitespaces(&line);
            arr[iter++] = line;
        }

        fs.close();
    } else
        cout << "Mkfile pls...\n";

    for (int i = 0; i < iter; i++)
        fill_line(arr[i], i);

    //for (auto& it : marks)
    //    cout << it.first << " : " << it.second + 1 << '\n';

    regs[spec["sp"]] = 2097144;
    for (regs[31] = start_pos; regs[31] != end_pos; regs[31]++) {
        if (mem[regs[31]].first == -1)
            continue;

        cout << mem[regs[31]].first << " ";
        for (auto& it : mem[regs[31]].second)
            cout << it << " ";
        cout << endl;

        funcs[mem[regs[31]].first].func({mem[regs[31]].second[0], mem[regs[31]].second[1],
                                              mem[regs[31]].second[2], mem[regs[31]].second[3],
                                              mem[regs[31]].second[4]});

        if (exit0)
            break;
    }

    /*
    for (int i = 0; i < 50; i++) {
        cout << mem[i].first << " ";
        for (auto& it : mem[i].second)
            cout << it << " ";
        cout << '\n';
    }
     */
}