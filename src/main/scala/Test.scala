import scala.meta._

object Test {
  def main(args: Array[String]): Unit = {
    val stream = getClass.getResourceAsStream("Ordering.scala")
    val tree = stream.parse[Source]
  }
}