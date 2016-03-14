
class Author {
  def book(): Book = new Book()
}

class Book {
  def author: Author = new Author()
}

new Book()

