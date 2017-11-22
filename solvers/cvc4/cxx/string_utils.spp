#ifndef GPID_CVC4_STRING_UTILS_SPP
#define GPID_CVC4_STRING_UTILS_SPP

namespace gpid {
namespace stringUtils {
    static inline void ltrim(std::string &s) {
        s.erase(s.begin(), std::find_if(s.begin(), s.end(), [](int ch) {
                    return !std::isspace(ch);
                }));
    }
    static inline void rtrim(std::string &s) {
        s.erase(std::find_if(s.rbegin(), s.rend(), [](int ch) {
                    return !std::isspace(ch);
                }).base(), s.end());
    }
    static inline void trim(std::string &s) {
        ltrim(s);
        rtrim(s);
    }

    template<typename Out>
    static inline void split(const std::string &s, char delim, Out result) {
        std::stringstream ss(s);
        std::string item;
        while (std::getline(ss, item, delim)) {
            trim(item);
            if (item != "") {
                *(result++) = item;
            }
        }
    }
    static inline std::vector<std::string> split(const std::string &s, char delim) {
        std::vector<std::string> elems;
        split(s, delim, std::back_inserter(elems));
        return elems;
    }
    static inline std::string first(const std::string &s, char delim)
    { return split(s, delim)[0]; }
    static inline std::string second(const std::string &s, char delim)
    { return split(s, delim)[1]; }
}
}

#endif
