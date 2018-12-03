#ifndef LIB_UGLY__MFFF_HPP
#define LIB_UGLY__MFFF_HPP

#include <set>
#include <map>
#include <list>
#include <string>
#include <vector>
#include <fstream>

namespace ugly {

    using namespace std;

    inline static const string untighten(const string& s) {
        return s.at(0) == '!' ? s.substr(1) : s;
    }

    inline static map<string, list<vector<string>>> get_modulo_appls(const std::string& filename) {
        ifstream source(filename);
        map<string, list<vector<string>>> res;
        string line;
        while (getline(source, line)) {
            if (line.find("mod ") != string::npos) {
                size_t p0 = line.find("mod ");
                size_t p1 = line.find(" ", p0+4);
                size_t p2 = line.find(" ", p1+1);
                res["mod" + line.substr(p1+1, p2-p1-1)].push_back({untighten(line.substr(p0+4, p1-p0-4))});
            }
        }
        source.close();
        return res;
    }

}

#endif
