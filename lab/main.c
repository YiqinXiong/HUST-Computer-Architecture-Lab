#include <string.h>
#include <stdio.h>

int main()
{
    char buf[1000] = " L 10,4";
    char c;
    unsigned long long ll;
    int len;
    sscanf(buf, "%c %llx,%d", &c, &ll, &len);
    printf("%c,%lld,%d\n", c, ll, len);
}