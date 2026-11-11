#ifndef _UTILITY_H_
#define _UTILITY_H_

#include <ctime>
#include <cstdlib>
#include <cstdio>
#include <cmath>
#include <cstring>
#include <string>
#include <vector>
#include <algorithm>
#include <sstream>
#include <iostream>
#include <tuple>
#include <queue>
#include <set>
#include <unordered_set>
#include <unordered_map>
#include <functional>
#include <cassert>
using namespace std;

#define _HEURISTIC_
#define _REDUCTION_RULE_
#define _QUERY_DECOMPOSITION_

using ui = unsigned int;  // vertex type
using ept = unsigned int; // edge pointer type; unsigned int can be used to process up to two billion undirected edges

#define pb push_back

class Utility
{
public:
	static std::string integer_to_string(long long number)
	{
		std::vector<ui> sequence;
		if (number == 0)
			sequence.pb(0);
		while (number > 0)
		{
			sequence.pb(number % 1000);
			number /= 1000;
		}

		char buf[5];
		std::string res;
		for (ui i = sequence.size(); i > 0u; i--)
		{
			if (i == sequence.size())
				sprintf(buf, "%u", sequence[i - 1]);
			else
				sprintf(buf, ",%03u", sequence[i - 1]);
			res += std::string(buf);
		}
		return res;
	}
};

#endif
