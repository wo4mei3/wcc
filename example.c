static struct X{int x;} func(struct Y{void *y;} a) {
    return (struct X){0};
}
int main () {
    return 0;
}