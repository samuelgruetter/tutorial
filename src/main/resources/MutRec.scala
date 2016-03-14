
object MutRec {
  class Author {
    def book(): Book = new Book()
  }

  class Book {
    def author(): Author = new Author()
  }


  def run(): Book = {
    new Book().author().book()
  }
}
