/**
 * implement a container like std::map
 *
 * Red-Black Tree implementation with a sentinel header node:
 *   header->parent == root of the tree (nullptr when empty)
 *   header->left   == leftmost (minimum) node (header itself when empty)
 *   header->right  == rightmost (maximum) node (header itself when empty)
 * The sentinel never carries data, so no default constructor of Key/T
 * is ever required, and end() iterators stay valid across insertions.
 */
#ifndef SJTU_MAP_HPP
#define SJTU_MAP_HPP

// only for std::less<T>
#include <functional>
#include <cstddef>
#include "utility.hpp"
#include "exceptions.hpp"

namespace sjtu {

template<
    class Key,
    class T,
    class Compare = std::less<Key>
> class map {
  public:
    /**
     * the internal type of data.
     * it should have a default constructor, a copy constructor.
     * You can use sjtu::map as value_type by typedef.
     */
    typedef pair<const Key, T> value_type;

  private:
    struct node_base {
        node_base *parent;
        node_base *left;
        node_base *right;
        bool red;
        node_base() : parent(nullptr), left(nullptr), right(nullptr), red(false) {}
    };

    struct node : public node_base {
        value_type data;
        explicit node(const value_type &v) : node_base(), data(v) {}
    };

    node_base *header;
    size_t cnt;
    Compare comp;

    static node_base *min_node(node_base *x) {
        while (x->left) x = x->left;
        return x;
    }

    static node_base *max_node(node_base *x) {
        while (x->right) x = x->right;
        return x;
    }

    /* in-order successor; returns hdr when x is the last element. */
    static node_base *next_node(node_base *x, node_base *hdr) {
        if (x->right) return min_node(x->right);
        node_base *y = x->parent;
        while (y != hdr && x == y->right) {
            x = y;
            y = y->parent;
        }
        return y;
    }

    /* in-order predecessor; returns nullptr when there is none. */
    static node_base *prev_node(node_base *x, node_base *hdr) {
        if (x->left) return max_node(x->left);
        node_base *y = x->parent;
        while (y != hdr && x == y->left) {
            x = y;
            y = y->parent;
        }
        if (y == hdr) return nullptr;
        return y;
    }

    void left_rotate(node_base *x) {
        node_base *y = x->right;
        x->right = y->left;
        if (y->left) y->left->parent = x;
        y->parent = x->parent;
        if (x->parent == header) header->parent = y;
        else if (x == x->parent->left) x->parent->left = y;
        else x->parent->right = y;
        y->left = x;
        x->parent = y;
    }

    void right_rotate(node_base *x) {
        node_base *y = x->left;
        x->left = y->right;
        if (y->right) y->right->parent = x;
        y->parent = x->parent;
        if (x->parent == header) header->parent = y;
        else if (x == x->parent->right) x->parent->right = y;
        else x->parent->left = y;
        y->right = x;
        x->parent = y;
    }

    void insert_fixup(node_base *z) {
        while (z->parent->red) {
            node_base *gp = z->parent->parent;
            if (z->parent == gp->left) {
                node_base *uncle = gp->right;
                if (uncle && uncle->red) {
                    z->parent->red = false;
                    uncle->red = false;
                    gp->red = true;
                    z = gp;
                } else {
                    if (z == z->parent->right) {
                        z = z->parent;
                        left_rotate(z);
                    }
                    z->parent->red = false;
                    z->parent->parent->red = true;
                    right_rotate(z->parent->parent);
                }
            } else {
                node_base *uncle = gp->left;
                if (uncle && uncle->red) {
                    z->parent->red = false;
                    uncle->red = false;
                    gp->red = true;
                    z = gp;
                } else {
                    if (z == z->parent->left) {
                        z = z->parent;
                        right_rotate(z);
                    }
                    z->parent->red = false;
                    z->parent->parent->red = true;
                    left_rotate(z->parent->parent);
                }
            }
        }
        header->parent->red = false;
    }

    /* replace the subtree rooted at u with the subtree rooted at v */
    void transplant(node_base *u, node_base *v) {
        if (u->parent == header) header->parent = v;
        else if (u == u->parent->left) u->parent->left = v;
        else u->parent->right = v;
        if (v) v->parent = u->parent;
    }

    /* x may be nullptr; xp is the parent of the (possibly null) node x. */
    void delete_fixup(node_base *x, node_base *xp) {
        while (x != header->parent && (x == nullptr || !x->red)) {
            node_base *parent = x ? x->parent : xp;
            if (parent == header) break; // x is the root; nothing to fix
            if (x == parent->left) {
                node_base *w = parent->right;
                if (w->red) {
                    w->red = false;
                    parent->red = true;
                    left_rotate(parent);
                    w = parent->right;
                }
                if ((w->left == nullptr || !w->left->red) &&
                    (w->right == nullptr || !w->right->red)) {
                    w->red = true;
                    x = parent;
                    xp = parent->parent;
                } else {
                    if (w->right == nullptr || !w->right->red) {
                        if (w->left) w->left->red = false;
                        w->red = true;
                        right_rotate(w);
                        w = parent->right;
                    }
                    w->red = parent->red;
                    parent->red = false;
                    if (w->right) w->right->red = false;
                    left_rotate(parent);
                    x = header->parent;
                    xp = header;
                }
            } else {
                node_base *w = parent->left;
                if (w->red) {
                    w->red = false;
                    parent->red = true;
                    right_rotate(parent);
                    w = parent->left;
                }
                if ((w->right == nullptr || !w->right->red) &&
                    (w->left == nullptr || !w->left->red)) {
                    w->red = true;
                    x = parent;
                    xp = parent->parent;
                } else {
                    if (w->left == nullptr || !w->left->red) {
                        if (w->right) w->right->red = false;
                        w->red = true;
                        left_rotate(w);
                        w = parent->left;
                    }
                    w->red = parent->red;
                    parent->red = false;
                    if (w->left) w->left->red = false;
                    right_rotate(parent);
                    x = header->parent;
                    xp = header;
                }
            }
        }
        if (x) x->red = false;
    }

    node_base *find_node(const Key &key) const {
        node_base *x = header->parent;
        while (x) {
            if (comp(key, static_cast<node *>(x)->data.first)) x = x->left;
            else if (comp(static_cast<node *>(x)->data.first, key)) x = x->right;
            else return x;
        }
        return nullptr;
    }

    /* deep copy the subtree rooted at src, hanging it under parent. */
    node_base *clone(node_base *src, node_base *parent) {
        node_base *copy = new node(static_cast<node *>(src)->data);
        copy->red = src->red;
        copy->parent = parent;
        if (src->left) copy->left = clone(src->left, copy);
        if (src->right) copy->right = clone(src->right, copy);
        return copy;
    }

    void destroy(node_base *x) {
        if (x == nullptr) return;
        destroy(x->left);
        destroy(x->right);
        delete static_cast<node *>(x);
    }

  public:
    class const_iterator;

    class iterator {
        friend class map;
        friend class const_iterator;

      private:
        node_base *ptr;
        node_base *hdr;
        iterator(node_base *p, node_base *h) : ptr(p), hdr(h) {}

      public:
        iterator() : ptr(nullptr), hdr(nullptr) {}

        iterator(const iterator &other) : ptr(other.ptr), hdr(other.hdr) {}

        /**
         * iter++
         */
        iterator operator++(int) {
            iterator old(*this);
            ++(*this);
            return old;
        }

        /**
         * ++iter
         */
        iterator &operator++() {
            if (ptr == nullptr || ptr == hdr) throw invalid_iterator();
            ptr = next_node(ptr, hdr);
            return *this;
        }

        /**
         * iter--
         */
        iterator operator--(int) {
            iterator old(*this);
            --(*this);
            return old;
        }

        /**
         * --iter
         */
        iterator &operator--() {
            if (ptr == nullptr || hdr == nullptr) throw invalid_iterator();
            if (ptr == hdr) {
                if (hdr->parent == nullptr) throw invalid_iterator();
                ptr = hdr->right;
                return *this;
            }
            node_base *p = prev_node(ptr, hdr);
            if (p == nullptr) throw invalid_iterator();
            ptr = p;
            return *this;
        }

        /**
         * a operator to check whether two iterators are same (pointing to the same memory).
         */
        value_type &operator*() const {
            if (ptr == nullptr || ptr == hdr) throw invalid_iterator();
            return static_cast<node *>(ptr)->data;
        }

        bool operator==(const iterator &rhs) const { return ptr == rhs.ptr; }

        bool operator==(const const_iterator &rhs) const { return ptr == rhs.ptr; }

        /**
         * some other operator for iterator.
         */
        bool operator!=(const iterator &rhs) const { return ptr != rhs.ptr; }

        bool operator!=(const const_iterator &rhs) const { return ptr != rhs.ptr; }

        /**
         * for the support of it->first.
         */
        value_type *operator->() const noexcept {
            return &(static_cast<node *>(ptr)->data);
        }
    };

    class const_iterator {
        friend class map;
        friend class iterator;

      private:
        node_base *ptr;
        node_base *hdr;
        const_iterator(node_base *p, node_base *h) : ptr(p), hdr(h) {}

      public:
        const_iterator() : ptr(nullptr), hdr(nullptr) {}

        const_iterator(const const_iterator &other) : ptr(other.ptr), hdr(other.hdr) {}

        const_iterator(const iterator &other) : ptr(other.ptr), hdr(other.hdr) {}

        const_iterator operator++(int) {
            const_iterator old(*this);
            ++(*this);
            return old;
        }

        const_iterator &operator++() {
            if (ptr == nullptr || ptr == hdr) throw invalid_iterator();
            ptr = next_node(ptr, hdr);
            return *this;
        }

        const_iterator operator--(int) {
            const_iterator old(*this);
            --(*this);
            return old;
        }

        const_iterator &operator--() {
            if (ptr == nullptr || hdr == nullptr) throw invalid_iterator();
            if (ptr == hdr) {
                if (hdr->parent == nullptr) throw invalid_iterator();
                ptr = hdr->right;
                return *this;
            }
            node_base *p = prev_node(ptr, hdr);
            if (p == nullptr) throw invalid_iterator();
            ptr = p;
            return *this;
        }

        const value_type &operator*() const {
            if (ptr == nullptr || ptr == hdr) throw invalid_iterator();
            return static_cast<node *>(ptr)->data;
        }

        bool operator==(const const_iterator &rhs) const { return ptr == rhs.ptr; }

        bool operator==(const iterator &rhs) const { return ptr == rhs.ptr; }

        bool operator!=(const const_iterator &rhs) const { return ptr != rhs.ptr; }

        bool operator!=(const iterator &rhs) const { return ptr != rhs.ptr; }

        const value_type *operator->() const noexcept {
            return &(static_cast<node *>(ptr)->data);
        }
    };

    /**
     * two constructors
     */
    map() : header(new node_base()), cnt(0), comp(Compare()) {
        header->left = header->right = header;
    }

    map(const map &other) : header(new node_base()), cnt(0), comp(other.comp) {
        header->left = header->right = header;
        if (other.header->parent) {
            header->parent = clone(other.header->parent, header);
            header->left = min_node(header->parent);
            header->right = max_node(header->parent);
            cnt = other.cnt;
        }
    }

    /**
     * assignment operator
     */
    map &operator=(const map &other) {
        if (this == &other) return *this;
        clear();
        if (other.header->parent) {
            header->parent = clone(other.header->parent, header);
            header->left = min_node(header->parent);
            header->right = max_node(header->parent);
            cnt = other.cnt;
        }
        return *this;
    }

    /**
     * destructor
     */
    ~map() {
        clear();
        delete header;
    }

    /**
     * access specified element with bounds checking
     * Returns a reference to the mapped value of the element with key equivalent to key.
     * If no such element exists, an exception of type `index_out_of_bound'
     */
    T &at(const Key &key) {
        node_base *x = find_node(key);
        if (x == nullptr) throw index_out_of_bound();
        return static_cast<node *>(x)->data.second;
    }

    const T &at(const Key &key) const {
        node_base *x = find_node(key);
        if (x == nullptr) throw index_out_of_bound();
        return static_cast<node *>(x)->data.second;
    }

    /**
     * access specified element
     * Returns a reference to the value that is mapped to a key equivalent to key,
     *   performing an insertion if such key does not already exist.
     */
    T &operator[](const Key &key) {
        node_base *x = find_node(key);
        if (x) return static_cast<node *>(x)->data.second;
        return insert(value_type(key, T())).first->second;
    }

    /**
     * behave like at() throw index_out_of_bound if such key does not exist.
     */
    const T &operator[](const Key &key) const {
        node_base *x = find_node(key);
        if (x == nullptr) throw index_out_of_bound();
        return static_cast<node *>(x)->data.second;
    }

    /**
     * return a iterator to the beginning
     */
    iterator begin() { return iterator(header->left, header); }

    const_iterator cbegin() const { return const_iterator(header->left, header); }

    /**
     * return a iterator to the end
     * in fact, it returns past-the-end.
     */
    iterator end() { return iterator(header, header); }

    const_iterator cend() const { return const_iterator(header, header); }

    /**
     * checks whether the container is empty
     * return true if empty, otherwise false.
     */
    bool empty() const { return cnt == 0; }

    /**
     * returns the number of elements.
     */
    size_t size() const { return cnt; }

    /**
     * clears the contents
     */
    void clear() {
        destroy(header->parent);
        header->parent = nullptr;
        header->left = header->right = header;
        cnt = 0;
    }

    /**
     * insert an element.
     * return a pair, the first of the pair is
     *   the iterator to the new element (or the element that prevented the insertion),
     *   the second one is true if insert successfully, or false.
     */
    pair<iterator, bool> insert(const value_type &value) {
        node_base *parent = header;
        node_base *x = header->parent;
        bool to_left = true;
        while (x) {
            parent = x;
            if (comp(value.first, static_cast<node *>(x)->data.first)) {
                x = x->left;
                to_left = true;
            } else if (comp(static_cast<node *>(x)->data.first, value.first)) {
                x = x->right;
                to_left = false;
            } else {
                return pair<iterator, bool>(iterator(x, header), false);
            }
        }
        node_base *z = new node(value);
        z->red = true;
        z->parent = parent;
        if (parent == header) header->parent = z;
        else if (to_left) parent->left = z;
        else parent->right = z;
        if (header->left == header ||
            comp(value.first, static_cast<node *>(header->left)->data.first)) {
            header->left = z;
        }
        if (header->right == header ||
            comp(static_cast<node *>(header->right)->data.first, value.first)) {
            header->right = z;
        }
        ++cnt;
        insert_fixup(z);
        return pair<iterator, bool>(iterator(z, header), true);
    }

    /**
     * erase the element at pos.
     *
     * throw if pos pointed to a bad element (pos == this->end() || pos points an element out of this)
     */
    void erase(iterator pos) {
        node_base *z = pos.ptr;
        if (pos.hdr != header || z == nullptr || z == header) throw invalid_iterator();
        node_base *y = z;
        bool y_red = y->red;
        node_base *x = nullptr;
        node_base *xp = nullptr;
        if (z->left == nullptr) {
            x = z->right;
            xp = z->parent;
            transplant(z, z->right);
        } else if (z->right == nullptr) {
            x = z->left;
            xp = z->parent;
            transplant(z, z->left);
        } else {
            y = min_node(z->right);
            y_red = y->red;
            x = y->right;
            if (y->parent == z) {
                if (x) x->parent = y;
                xp = y;
            } else {
                transplant(y, y->right);
                xp = y->parent;
                y->right = z->right;
                y->right->parent = y;
            }
            transplant(z, y);
            y->left = z->left;
            y->left->parent = y;
            y->red = z->red;
        }
        if (!y_red) delete_fixup(x, xp);
        if (header->parent) {
            header->left = min_node(header->parent);
            header->right = max_node(header->parent);
        } else {
            header->left = header->right = header;
        }
        delete static_cast<node *>(z);
        --cnt;
    }

    /**
     * Returns the number of elements with key
     *   that compares equivalent to the specified argument,
     *   which is either 1 or 0
     *     since this container does not allow duplicates.
     */
    size_t count(const Key &key) const { return find_node(key) ? 1 : 0; }

    /**
     * Finds an element with key equivalent to key.
     * key value of the element to search for.
     * Iterator to an element with key equivalent to key.
     *   If no such element is found, past-the-end (see end()) iterator is returned.
     */
    iterator find(const Key &key) {
        node_base *x = find_node(key);
        return x ? iterator(x, header) : end();
    }

    const_iterator find(const Key &key) const {
        node_base *x = find_node(key);
        return x ? const_iterator(x, header) : cend();
    }
};

}

#endif
