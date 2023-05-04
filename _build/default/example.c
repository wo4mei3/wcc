static struct X{int x;} func(struct Y{void *y;} a) {
    return (struct X){0};
}
int main () {
    struct Y a; 
    struct Y{int a;};
    return 0;
}