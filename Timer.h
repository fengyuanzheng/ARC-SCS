/******************************************************************************
 * timer.h
 * record the elapsed time in microseconds (10^{-6} second)
 *****************************************************************************/

#ifndef _TIMER_LJ_
#define _TIMER_LJ_

#include <chrono>

class Timer
{
public:
	Timer() { m_start = timestamp(); }
	void restart() { m_start = timestamp(); }
	long long elapsed() { return timestamp() - m_start; }

private:
	long long m_start;

	// A monotonic clock keeps elapsed measurements stable during clock corrections.
	long long timestamp()
	{
		using namespace std::chrono;
		return duration_cast<microseconds>(steady_clock::now().time_since_epoch()).count();
	}
};

#endif
