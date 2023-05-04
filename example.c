static struct X{int x;} func(struct Y{void *y;} a) {
    return (struct X){0};
}

extern int printf(const char *, ...);

int main () {
    goto label;
    struct Y a; 
    struct Y{int a;};
label :
    for (int i=0;i<5;i++){
        printf("%d",i);
        break;continue;
    }
return 0;
}